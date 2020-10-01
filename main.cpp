#include <QCoreApplication>
#include <iostream> // stderr
#include <cstdio>
#include <memory>
#include <map>
#include <stdexcept>
#include <string> // string manipulation
#include <array>
#include <vector>
#include <algorithm>
#include <cctype>
#include <locale>
#include <cstdlib>    // os.getenv
#include <filesystem> // os.path
#include <unistd.h>   // subprocesss command, getlogin() for getpass.getuser()
#include <sys/file.h> // flock() to create & lock a file
#include <regex>      // regex_search() for re.search(), regex_constants::icase for re.I, regex_replace() for re.sub()
#include <fstream>
#include <cmath>
#include <sstream>
#include <chrono>             // monotonic()
#include <QCommandLineParser> // command line parser
#include <QSysInfo>

using namespace std;
namespace fs = filesystem;

typedef string (*confFn)(string);

#define PROGPATH fs::current_path()
#define PROGNAME PROGPATH.stem()

// Conf file containing gesture commands.
// Search first for user file then system file.
#define CONFNAME PROGNAME.concat(".conf")
string USERDIR = getenv("XDG_CONFIG_HOME") != NULL ? getenv("XDG_CONFIG_HOME") : fs::path(getenv("HOME")).append(".config");
vector<string> CONFDIRS = {USERDIR, "/etc"};

// Ratio of X/Y (or Y/X) at which we consider an oblique swipe gesture.
// The number is the trigger angle in degrees and set to 360/8/2.
//#define PI 2 * acos(0.0)
//#define RADIANS(x) (x * PI) / 180
//#define OBLIQUE_RATIO tan(RADIAN(22.5))
#define OBLIQUE_RATIO 0.41421356237309503

// Default minimum significant distance to move for swipes, in dots.
// Can be changed using configuration command.
int swipe_min_threshold = 0;
map<string, string> args = {};
int abzsquare = 0;

// Timeout on gesture action from start to end. 0 = no timeout. In secs.
// Can be changed using configuration command.
float DEFAULT_TIMEOUT = 1.5;
float timeoutv = DEFAULT_TIMEOUT;

// Rotation threshold in degrees to discriminate pinch rotate from in/out
float ROTATE_ANGLE = 15.0;

// -------------- HELPER FUNCS -------------------- //
inline void ltrim(string &s)
{
    s.erase(s.begin(), find_if(s.begin(), s.end(), [](int ch) {
                return !isspace(ch);
            }));
}

// trim from end (in place)
inline void rtrim(string &s)
{
    s.erase(find_if(s.rbegin(), s.rend(), [](int ch) {
                return !isspace(ch);
            }).base(),
            s.end());
}

// trim from both ends (in place)
inline void trim(string &s)
{
    ltrim(s);
    rtrim(s);
}

inline void removeTrailingCharacters(string &str, const char charToRemove = ' ')
{
    str.erase(str.find_last_not_of(charToRemove) + 1, string::npos);
}

const string platform()
{
    ostringstream stream;
    stream << QSysInfo::kernelType().toStdString() << "-" << QSysInfo::kernelVersion().toStdString() << "-" << QSysInfo::currentCpuArchitecture().toStdString();
    return stream.str();
}

inline string expand_env(string text)
{
    static const regex env_re{R"--(\$\{([^}]+)\})--"};
    smatch match;
    while (regex_search(text, match, env_re))
    {
        auto const from = match[0];
        auto const var_name = match[1].str().c_str();
        text.replace(from.first, from.second, getenv(var_name));
    }
    return text;
}

string join(const vector<string>& v, const string& c = " ")
{
    string res = "";
    for (vector<string>::const_iterator p = v.begin(); p != v.end(); ++p)
    {
        res += *p;
        if (p != v.end() - 1)
            res += c;
    }
    return res;
}

vector<string> splitStrings(string str, const char& dl = ' ', const int& maxsplit = numeric_limits<int>::max())
{
    string word = "";
    str = str + dl;
    vector<string> substr_list;
    int split_cnt = 0;
    for (int i = 0; i < (int)str.size(); i++)
    {
        if (split_cnt < maxsplit)
        {
            if (str[i] != dl)
                word += str[i];

            else
            {
                if ((int)word.size() != 0)
                {
                    substr_list.push_back(word);
                    split_cnt++;
                }
                word = "";
            }
        }
        else
        {
            word = str.substr(i, str.size() - (i + 1));
            substr_list.push_back(word);
            break;
        }
    }

    // return the splitted strings
    return substr_list;
}

vector<string> split_shell(string command)
{
    regex rx("([^(\")]\\S*|(\").+?(\"))\\s*");
    smatch res;
    vector<string> result = {};
    while (regex_search(command, res, rx))
    {
        result.push_back(res[0]);
        command = res.suffix().str();
    }
    return result;
}

int getIndex(const vector<string>& v, const string& K)
{
    auto it = find(v.begin(), v.end(), K);
    if (it != v.end()) return distance(v.begin(), it);
    else  return -1;
}

bool is_digits(const string& str)
{
    return all_of(str.begin(), str.end(), ::isdigit); // C++11
}

void Parse(int result[3], const string &input)
{
    istringstream parser(input);
    parser >> result[0];
    for (int idx = 1; idx < 3; idx++)
    {
        parser.get(); //Skip period
        parser >> result[idx];
    }
}

bool LessThanVersion(const string &a, const string &b)
{
    int parsedA[3], parsedB[3];
    Parse(parsedA, a);
    Parse(parsedB, b);
    return lexicographical_compare(parsedA, parsedA + 3, parsedB, parsedB + 3);
}

vector<string> resplit(const string &s, const string &rgx_str = "\\s+")
{
    vector<string> result;
    regex rgx(rgx_str);

    sregex_token_iterator iter(s.begin(), s.end(), rgx, -1);
    sregex_token_iterator end;

    while (iter != end)
    {
        result.push_back(*iter);
        ++iter;
    }

    return result;
}

string exec(const char *cmd, bool check = true)
{
    array<char, 128> buffer;
    string result;
    try
    {
        unique_ptr<FILE, decltype(&pclose)> pipe(popen(cmd, "r"), pclose);

        while (fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr)
        {
            result += buffer.data();
        }
    }
    catch (runtime_error const &e)
    {
        result = check ? e.what() : NULL;
    }
    return result;
}
// -------------- HELPER FUNCS -------------------- //

FILE *open_lock(const vector<string> &arr)
{
    // Create a lock based on given list of arguments
    FILE *f = fopen(string("/tmp/" + join(arr, "-") + ".lock").c_str(), "w");
    try
    {
        if (flock(fileno(f), LOCK_EX | LOCK_NB) == -1)
            return NULL;
    }
    catch (system_error &e)
    {
        return NULL;
    }

    return f;
}

string run(const vector<string> &cmd, bool check = true, bool block = true)
{
    // Run function and return standard output, Popen() handle, or None
    string result;
    string str_cmd = join(cmd);
    try
    {
        if (block)
            result = exec(str_cmd.c_str(), check);
        else
            result = system(str_cmd.c_str());
    }
    catch (const exception &e)
    {
        if (check)
            cerr << e.what() << endl;
    }

    return result;
}

string get_libinput_vers()
{
    // Return the libinput installed version number string
    // Try to use newer libinput interface then fall back to old
    // (depreciated) interface.
    string res = run({"libinput", "--version"}, false);
    trim(res);
    if (!res.length())
        res = run({"libinput-list-devices", "--version"}, false);
    return res;
}

vector<map<string, string>> get_devices_list(const string &cmd_list_devices, const string &device_list)
{
    // Get list of devices and their attributes (as a dict) from libinput
    string stdout;
    if (device_list.length())
    {
        ifstream fd;
        try
        {
            fd.open(device_list);
            streamsize size = fd.tellg();
            fd.seekg(0, ios::beg);

            char *buffer = new char[size];
            if (fd.read(buffer, size))
            {
                stdout = buffer;
            }
        }
        catch (const exception &e)
        {
            fd.close();
        }
        fd.close();
    }
    else
    {
        stdout = run(splitStrings(cmd_list_devices));
    }

    vector<map<string, string>> device_list_info;
    map<string, string> dev = {};
    if (stdout.length())
    {
        vector<string> arr_stdout;
        stringstream ss(stdout);
        string info;

        while (getline(ss, info, '\n'))
        {
            arr_stdout.push_back(info);
        }

        for (string line : arr_stdout)
        {
            trim(line);
            if (line.length() && line.find(":"))
            {
                vector<string> key_value = splitStrings(line, ':', 1);
                trim(key_value.at(0));
                trim(key_value.at(1));
                transform(key_value[0].begin(), key_value[0].end(), key_value[0].begin(), ::tolower);
                dev.insert({key_value.at(0), key_value.at(1)});
            }
            else if (dev.size())
            {
                device_list_info.push_back(dev);
                dev = {};
            }
        }
        // Ensure we include last device
        if (dev.size())
            return device_list_info;
    }
    return device_list_info;
}

map<string, string> get_device_info(const string &name, const string &cmd_list_devices, const string &device_list) {
    // Determine libinput touchpad device and return device info
    vector<map<string, string>> devices = get_devices_list(cmd_list_devices, device_list);
    if (devices.empty()) {
        cerr << "Can not see any devices, did you add yourself to the input group and log out/in?" << endl;
        return {};
    }

    if (name.length()) {
        string kdev = (name[0] == '/') ? fs::absolute(fs::path(name)) : "";
        for (map<string, string> d : devices) {
            if (kdev.length()) {
                if (d["kernel"] == kdev) return d;
            }
            else if (d["device"] == name) return d;
        }
        return {};
    }

    for (map<string, string> d : devices) 
        if (d.find("size") != d.end() && d["capabilities"].find("pointer")) return d;

    for (string txt : {"touch ?pad", "track ?pad"})
        for (map<string, string> d : devices) {
            smatch m;
            if (regex_search(d["Device"], m, regex(txt, regex_constants::icase))) return d;
        }
    return {};
}

map<string, string> get_device(const string &name, const string &cmd_list_devices, const string &device_list) {
    // Determine libinput touchpad device and add fixed path info
    map<string, string> dev = get_device_info(name, cmd_list_devices, device_list);

    if (dev.size())
    {
        string devname = dev["kernel"];
        string evname = "";
        if (devname.length())
        {
            fs::path devpath(devname);

            // Also determine and prefer a non-volatile path merely
            // because it is more identifying for users.
            for (string dirstr : {"/dev/input/by-path", "/dev/input/by-id"})
            {
                fs::path dirpath(dirstr);

                if (fs::exists(dirpath))
                {
                    for (const auto &path : fs::directory_iterator(dirpath))
                    {
                        if (fs::absolute(path) == devpath)
                        {
                            devname = path.path().string();
                            evname = string("(").append(devpath.filename().string() + ")");
                            break;
                        }
                    }
                    if (evname.length())
                        break;
                }
            }
        }

        dev["_path"] = devname;
        dev["_diag"] = string(devname).append(evname + ": " + dev["device"]);
    }

    return dev;
}

class COMMAND
{
    // Generic command handler
public:
    COMMAND() {}

    COMMAND(vector<string> arr_arg)
    {
        reprstr = join(arr_arg);
        // Expand '~' and env vars in executable command name
        string full_progpath = string(getenv("HOME")).append("/" + arr_arg[0]); 
        replace(arr_arg.begin(), arr_arg.end(), arr_arg[0], expand_env(full_progpath));
        argslist = arr_arg;
    }

    void Run()
    {
        // Run this command + arguments
        run(argslist, true, false);
    }

    friend ostream &operator<<(ostream &os, const COMMAND &cmd)
    {
        // Return string representation
        os << cmd.reprstr;
        return os;
    }

private:
    string reprstr;
    vector<string> argslist;
};

// Table of internal commands
map<string, COMMAND*> internal_commands = {};

void add_internal_command(COMMAND *cls)
{
    // Add configuration command to command lookup table based on name
    string key = regex_replace(typeid(cls).name(), regex("^COMMAND"), "");
    internal_commands.insert({key, cls});
}

class COMMAND_internal : public COMMAND
{
    // Internal command handler.
    // Commands currently supported follow. Each is configured with the (X,Y) translation to be applied to the desktop grid.
public:
    COMMAND_internal(const vector<string> arr_arg) : COMMAND(arr_arg),
        commands({
            {"ws_up", {0, 1}},
            {"ws_down", {0, -1}},
            {"ws_left", {1, 0}},
            {"ws_right", {-1, 0}},
            {"ws_left_up", {1, 1}},
            {"ws_left_down", {1, -1}},
            {"ws_left_down", {-1, 1}},
            {"ws_right_down", {-1, -1}}
        }),
        //        commands_list(
        //            for(auto entry : commands)
        //                commands_list.push_back(entry.first)
        //        ),
        CMDLIST(
            splitStrings("wmctrl -d")),
        CMDSET(
            splitStrings("wmctrl -s")) 
    {
        // Action internal swipe commandss
        for (auto const &[key, val] : commands)
            commands_list.push_back(key);

        // Set up command line arguments
        QCommandLineParser opt;
        opt.setApplicationDescription("Internal command handler.");
        opt.addHelpOption();
        QCommandLineOption wrapOpt(QStringList() << "w" << "wrap",
                                      QCoreApplication::translate("main", "wrap workspaces when switching to/from start/end"));
        opt.addOption(wrapOpt);
        QCommandLineOption colsOpt(QStringList() << "c" << "cols",
                                         QCoreApplication::translate("main", "number of columns in virtual desktop grid, default=1"));
        colsOpt.setDefaultValue("1");
        opt.addOption(colsOpt);
        QCommandLineOption rowOpt("row");
        rowOpt.setFlags(QCommandLineOption::HiddenFromHelp);
        rowOpt.setDefaultValue("0");
        opt.addOption(rowOpt);
        QCommandLineOption colOpt("col");
        colOpt.setFlags(QCommandLineOption::HiddenFromHelp);
        colOpt.setDefaultValue("0");
        opt.addOption(colOpt);
        QCommandLineOption actionOpt("action",
                                     QCoreApplication::translate("main", "Internal command to action"));
        QStringList actions;
        for(string cmd : commands_list)
            actions.append(QString::fromStdString(cmd));
        actionOpt.setDefaultValues(actions);
        opt.addOption(actionOpt);
        nowrap = !opt.isSet(wrapOpt);
        rows = 0;
        cols = 0;
        int cmdi = getIndex(commands_list, opt.value(actionOpt).toStdString());

        if(cmdi >= 2) {
            if(opt.value(rowOpt).toInt() || opt.value(colOpt).toInt()) throw("Legacy \"--row\" and \"--col\" not supported");
            if(!opt.isSet(colsOpt)) {
                if(cmdi < 4) {
                    cols = 1;
                    cmdi -= 2;
                }
                else throw("\"--cols\" must be specified");
            }
            else if(opt.value(colsOpt) < 1) throw("\"--cols\" must be >= 1");
            else cols = opt.value(colsOpt).toInt();
        }
        else {
            // Convert old legacy/depreciated arguments to new arguments
            if(opt.isSet(colsOpt)) {
                if(opt.value(colsOpt) < 1) throw("\"--cols\" must be >= 1");
                cols = opt.value(colsOpt).toInt();
            }
            else if(opt.isSet(rowOpt)) {
                cmdi += 2;
                cols = opt.value(rowOpt).toInt();
            }
            else if(opt.isSet(colOpt)) rows = opt.value(colOpt).toInt();
            else cols = 1;
        }
        // Save the translations appropriate to this command
        xmove = commands[cmdi][1][0];
        ymove = commands[cmdi][1][1];
    }

    string Run(bool block = false)
    {
        // Get list of current workspaces and select next one
        string stdout = run(CMDLIST, false);

        if (stdout.empty())
            stdout = "0 *\n1 -";

        // Parse the output of above command
        trim(stdout);
        vector<string> lines;
        stringstream ss(stdout);
        string tmp;

        while (getline(ss, tmp, '\n'))
        {
            lines.push_back(splitStrings(tmp, ' ', 2)[1]);
        }

        int start = getIndex(lines, "*"), index = start;
        int num = lines.size();
        int Cols = floor((cols ? cols : num) / rows);
        int numv = (floor((num - 1) / cols) + 1) * cols;

        // Calculate new workspace X direction index
        int count = xmove;
        if (count < 0)
        {
            if (index % Cols == 0)
            {
                if (nowrap)
                    return "";
                index += Cols - 1;
                if (index >= num)
                {
                    if (ymove == 0)
                    {
                        if (nowrap)
                            return "";
                        index = num - 1;
                    }
                }
            }
            else
            {
                index += count;
            }
        }
        else if (count > 0)
        {
            index += count;
            if (index % Cols == 0)
            {
                if (nowrap)
                    return "";
                index -= Cols;
            }
            else if (index >= num)
            {
                if (ymove == 0)
                {
                    if (nowrap)
                        return "";
                    index -= numv - index;
                }
            }
        }

        // Calculate new workspace Y direction index
        count = ymove * Cols;
        if (count < 0)
        {
            if (index < Cols && nowrap)
                return "";
            index = (index + count) % numv;
            if (index >= num)
                index += count;
        }
        else if (count > 0)
        {
            index += count;
            if (index >= numv)
            {
                if (nowrap)
                    return "";
                index = index % numv;
            }
            else if (index >= num)
            {
                if (nowrap)
                    return "";
                index = (index + count) % numv;
            }
        }

        // Switch to desired workspace
        if (index != start)
        {
            vector<string> cmd_set = CMDSET;
            cmd_set.push_back(to_string(index));
            return run(cmd_set, true, block);
        }
        return "";
    }

protected:
    const map<string, vector<int>> commands;
    vector<string> commands_list;
    const vector<string> CMDLIST, CMDSET;
    bool nowrap;
    int rows, cols, xmove, ymove;
};

class GESTURE
{
    // Abstract base class for handling for gestures
public:
    GESTURE()
    {
        // Initialise this gesture at program start
        name = typeid(this).name();
        motions = {};
        has_extended = false;
    }

    string add(string motion, string fingers, string command)
    {
        // Add a configured motion command for this gesture

        if (find(SUPPORTED_MOTIONS.begin(), SUPPORTED_MOTIONS.end(), motion) == SUPPORTED_MOTIONS.end())
        {
            ostringstream stream;
            stream << "Gesture " << name << " does not support motion \"" << motion << "\"." << endl
                   << "Must be \"" << join(SUPPORTED_MOTIONS, " or ") << "\"";
            return stream.str();
        }

        if (command == "")
            return "No command configured";

        // If any extended gestures configured then set flag to enable their discrimination
        if (motion.find(extended_text))
            has_extended = true;

        string key;
        if (fingers != "")
            key = fingers;
        else
            key = motion;

        vector<string> cmds = {};
        try
        {
            cmds = split_shell(command);
        }
        catch (const exception &e)
        {
            return e.what();
        }

        //            COMMAND cls = internal_commands[cmds[0]];

        try
        {
            //                motions[key] = cls(cmds);
        }
        catch (const exception &e)
        {
            return e.what();
        }

        return "";
    }

    void begin(string fingers)
    {
        _fingers = fingers;
        data = {0.0, 0.0};
        starttime = chrono::steady_clock::now();
    }

    void action(string motion)
    {
        // Action a motion command for this gesture
        COMMAND *command;
        if (motions.find(_fingers) != motions.end())
            command = new COMMAND(motions[_fingers]);
        else
            command = new COMMAND(motions[motion]);

        //            if(args["verbose"])
        vector<string> res = {};
        for (vector<float>::const_iterator p = data.begin(); p != data.end(); ++p)
        {
            res.push_back(to_string(*p));
        }
        cout << PROGNAME << ": " << name << " " << motion << " " << _fingers << " " << join(res, "-") << endl;
        if (command)
            cout << command << endl;

        chrono::duration<double> time_span = duration_cast<chrono::duration<double>>(chrono::steady_clock::now() - starttime);
        if (timeoutv > 0 && time_span.count() < timeoutv)
        {
            //                if(args["verbose"])
            cout << "Timeout - no action" << endl;
            return;
        }

        if (command)
            command->Run();
    }

    virtual bool update(vector<string> coords) = 0;
    virtual void end() = 0;

    map<string, COMMAND> Motions() const
    {
        return motions;
    };

    string Name() const
    {
        return name;
    }

protected:
    string name, _fingers, extended_text;
    map<string, COMMAND> motions;
    bool has_extended;
    vector<string> SUPPORTED_MOTIONS;
    vector<float> data;
    chrono::steady_clock::time_point starttime;
};

// Table of gesture handlers
map<string, GESTURE *> handlers = {};

void add_gesture_handler(GESTURE *cls)
{
    handlers.insert({typeid(cls).name(), cls});
}

class SWIPE : public GESTURE
{
    // Class to handle this type of gesture
public:
    SWIPE() : GESTURE(),
              SUPPORTED_MOTIONS({"left", "right", "up", "down", "left_up", "right_up", "left_down", "right_down"}),
              extended_text("_") {}

    bool update(vector<string> coords) override
    {
        // Update this gesture for a motion
        // Ignore this update if we can not parse the numbers we expect
        try
        {
            x = stof(coords[2]);
            y = stof(coords[3]);
        }
        catch (const exception &e)
        {
            return false;
        }

        GESTURE::data[0] += x;
        GESTURE::data[1] += y;
        return true;
    }

    void end() override
    {
        // Action this gesture at the end of a motion sequence
        x = GESTURE::data[0];
        y = GESTURE::data[1];
        abx = fabs(x);
        aby = fabs(y);

        // Require absolute distance movement beyond a small thresh-hold.
        if (pow(abx, 2) + pow(aby, 2) < abzsquare)
            return;

        // Discriminate left/right or up/down.
        // If significant movement in both planes the consider it a oblique swipe (but only if any are configured)

        string motion;
        if (abx < aby)
        {
            motion = (x < 0) ? "left" : "right";
            if (GESTURE::has_extended && abx > 0 && aby / abx > OBLIQUE_RATIO)
                motion += (y < 0) ? "_up" : "_down";
        }
        else
        {
            motion = (y < 0) ? "up" : "down";
            if (GESTURE::has_extended && aby > 0 && abx / aby > OBLIQUE_RATIO)
                motion = (x < 0) ? "left_" + motion : "right_" + motion;
        }
        GESTURE::action(motion);
    }

private:
    const vector<string> SUPPORTED_MOTIONS;
    const string extended_text;
    float x, y, abx, aby;
};

class PINCH : public GESTURE
{
    // Class to handle this type of gesture'
public:
    PINCH() : GESTURE(),
              SUPPORTED_MOTIONS({"in", "out", "clockwise", "anticlockwise"}),
              extended_text("clock") {}

    bool update(vector<string> coords) override
    {
        // Update this gesture for a motion
        // Ignore this update if we can not parse the numbers we expect
        try
        {
            x = stof(coords[4]);
            y = stof(coords[5]);
        }
        catch (const exception &e)
        {
            return false;
        }

        GESTURE::data[0] += x - 1.0;
        GESTURE::data[1] += y;
        return true;
    }

    void end() override
    {
        // Action this gesture at the end of a motion sequence
        ratio = GESTURE::data[0];
        angle = GESTURE::data[1];

        if (GESTURE::has_extended && fabs(angle) > ROTATE_ANGLE)
            GESTURE::action((angle >= 0.0) ? "clockwise" : "anticlockwise");
        else if (ratio != 0.0)
            GESTURE::action((ratio <= 0.0) ? "in" : "out");
    }

private:
    const vector<string> SUPPORTED_MOTIONS;
    const string extended_text;
    float x, y, ratio, angle;
};

map<string, confFn> conf_commands = {};

template <typename T, typename U>
void add_conf_command(function<U(U)> func, string lineargs)
{
    // Add configuration command to command lookup table based on name
    string key = regex_replace(typeid(func).name(), regex("^conf_"), "");
    conf_commands.insert({key, &func(lineargs)});
}

string conf_gesture(string lineargs)
{
    // Process a single gesture line in conf file
    vector<string> fields = splitStrings(lineargs, ' ', 2);

    if ((int)fields.size() > 3)
        return "Invalid gesture line - not enough fields";

    string gesture = fields.at(0);
    string motion = fields.at(1);
    string command = fields.at(2);
    transform(gesture.begin(), gesture.end(), gesture.begin(), ::toupper);
    GESTURE *handler = handlers[gesture];

    if (!handler)
    {
        vector<string> arr_motion;
        for (auto const& [motion, gesture] : handlers)
        {
            string formatted_motion = motion;
            transform(formatted_motion.begin(), formatted_motion.end(), formatted_motion.begin(), ::tolower);
            arr_motion.push_back(formatted_motion);
        }
        ostringstream stream;
        stream << "Gesture (" << gesture << ") is not supported.\nMust be (" << join(arr_motion, " or ") << ")";
        return stream.str();
    }

    // Gesture command can be configured with optional specific finger count so look for that
    vector<string> cmds = splitStrings(command, ' ', 2);
    string fingers = cmds[0];
    string fcommand = cmds[1];
    if (is_digits(fingers) && fingers.length() == 1)
        command = (fcommand != "") ? fcommand : "";
    else
        fingers = "";

    // Add the configured gesture
    transform(motion.begin(), motion.end(), motion.begin(), ::tolower);
    return handler->add(motion, fingers, command);
}

string conf_device(string lineargs)
{
    // Process a single device line in conf file
    // Command line overrides configuration file
    if (args["device"] == "")
    {
        args["device"] = lineargs;
    }

    return (args["device"] != "") ? "" : "No device specified";
}

string swipe_threshold(string lineargs)
{
    // Change swipe threshold
    try
    {
        swipe_min_threshold = stoi(lineargs);
    }
    catch (exception &e)
    {
        return "Must be integer value";
    }
    return (swipe_min_threshold >= 0) ? "" : "Must be >= 0";
}

string timeout(string lineargs)
{
    // Change gesture timeout
    try
    {
        timeoutv = stof(lineargs);
    }
    catch (exception &e)
    {
        return "Must be float value";
    }
    return (timeoutv >= 0) ? "" : "Must be >= 0";
}

string get_conf_line(string line)
{
    // Process a single line in conf file'
    vector<string> arr_line = splitStrings(line, ' ', 1);
    string key = arr_line[0];
    string argslist = arr_line[1];
    // Old format conf files may have a ":" appended to the key

    removeTrailingCharacters(key, ':');
    confFn conf_func = conf_commands[key];

    if (!conf_func)
    {
        vector<string> arr_conf_commands;
        for (auto const& [key, func] : conf_commands) 
            arr_conf_commands.push_back(key);

        ostringstream stream;
        stream << "Configuration command (" << key << ") is not supported.\nMust be (" << join(arr_conf_commands, " or ") << ")";
        return stream.str();
    }
    return (argslist != "") ? conf_func(argslist) : "";
}

void get_conf(string conffile, string confname)
{
    // Read given configuration file and store internal actions etc
    ifstream fp;
    try
    {
        fp.open(conffile);
        string line;
        int num = 0;
        while (getline(fp, line))
        {
            trim(line);
            num++;
            if (line == "" || line[0] == '#')
                continue;

            string errmsg = get_conf_line(line);
            if (errmsg != "")
            {
                cerr << "Error at line " << num << " in file " << confname << ":\n>> " << line << " <<\n"
                     << errmsg << "." << endl;
                exit(0);
            }
        }
    }
    catch (exception &e)
    {
        fp.close();
    }
    fp.close();
}

string unexpanduser(string cfile)
{
    // Return absolute path name, with $HOME replaced by ~
    fs::path relslash(fs::absolute(cfile));
    string relhome;
    try
    {
        relhome = relslash.relative_path().lexically_relative(getenv("HOME"));
    }
    catch (exception &e)
    {
        relhome = "";
    }
    fs::path homepath("~");
    return (relhome != "") ? homepath.append(relhome) : relslash;
}

// Search for configuration file. Use file given as command line argument, else look for file in search dir order.
string read_conf(string conffile, string defname)
{
    fs::path confpath;
    if (conffile != "")
    {
        confpath = fs::path(conffile);
        if (!fs::exists(confpath))
        {
            cerr << "Conf file (" << conffile << " does not exist." << endl;
            exit(0);
        }
    }
    else
    {
        for (string confdir : CONFDIRS)
        {
            confpath = fs::path(confdir).append(defname);
            if (fs::exists(confpath))
                break;
            else
            {
                vector<string> arr_path;
                for (string c : CONFDIRS)
                    arr_path.push_back(unexpanduser(fs::path(c)));
                cerr << "No file " << defname << " in " << join(arr_path, " or ") << "." << endl;
                exit(0);
            }
        }
    }

    // Hide any personal user dir/names from diag output
    string confname = unexpanduser(confpath);
    // Read and process the conf file
    get_conf(confpath, confname);
    return confname;
}

int main(int argc, char *argv[])
{
    QCoreApplication a(argc, argv);
    // QCommandLineParser opt;
    // opt.setApplicationDescription("Libinput Gesture");
    // opt.addHelpOption();
    // QCommandLineOption confOption(QStringList() << "c"
    //                                             << "conffile",
    //                               QCoreApplication::translate("main", "alternative configuration file"),
    //                               QCoreApplication::translate("main", "Configure File"));
    // opt.addOption(confOption);
    // QCommandLineOption verboseOption(QStringList() << "v"
    //                                                << "verbose",
    //                                  QCoreApplication::translate("main", "output diagnostic messages"));
    // opt.addOption(verboseOption);
    // QCommandLineOption debugOption(QStringList() << "d"
    //                                              << "debug",
    //                                QCoreApplication::translate("main", "output diagnostic messages only, do not action gestures"));
    // opt.addOption(debugOption);
    // QCommandLineOption rawOption(QStringList() << "r"
    //                                            << "raw",
    //                              QCoreApplication::translate("main", "output raw libinput debug-event messages only, do not action gestures"));
    // opt.addOption(rawOption);
    // QCommandLineOption listOption(QStringList() << "l"
    //                                             << "list",
    //                               QCoreApplication::translate("main", "just list out environment and configuration"));
    // opt.addOption(listOption);
    // QCommandLineOption deviceOption("device", QCoreApplication::translate("main", "explicit device name to use (or path if starts with /)"));
    // // hidden option to specify a file containing libinput list device output to parse
    // QCommandLineOption deviceListOption("device-list");
    // deviceListOption.setFlags(QCommandLineOption::HiddenFromHelp);
    // opt.addOption(deviceListOption);
    // opt.process(a);

    // if (opt.isSet(debugOption) || opt.isSet(rawOption) || opt.isSet(listOption))
    //     args["verbose"] = true;

    // // Libinput changed the way in which it's utilities are called
    // string libvers = get_libinput_vers();
    // if (libvers == "")
    // {
    //     cerr << "libinput helper tools do not seem to be installed?" << endl;
    //     exit(0);
    // }

    // string cmd_debug_events, cmd_list_devices;
    // if (!LessThanVersion(libvers, "1.8.0"))
    // {
    //     cmd_debug_events = "libinput debug-events";
    //     cmd_list_devices = "libinput list-devices";
    // }
    // else
    // {
    //     cmd_debug_events = "libinput-debug-events";
    //     cmd_list_devices = "libinput-list-devices";
    // }

    // if (args["verbose"] != "")
    // {
    //     // Output various info/version info
    //     string xsession = (getenv("XDG_SESSION_DESKTOP") != NULL) ? getenv("XDG_SESSION_DESKTOP") : (getenv("DESKTOP_SESSION") != NULL) ? getenv("DESKTOP_SESSION") : "unknown";
    //     string xtype = (getenv("XDG_SESSION_TYPE") != NULL) ? getenv("XDG_SESSION_TYPE") : "unknown";
    //     cout << PROGNAME << ": session " << xsession << "+" << xtype << " on " << platform() << ", libinput " << libvers << endl;

    //     // Output hash version/checksum of this program
    //     string vers = run({"md5sum", PROGPATH}, false);
    //     vers = (vers != "") ? splitStrings(vers, ' ')[0] : "?";
    //     cout << PROGPATH << ": hash " << vers << endl;
    // }

    // // Read and process the conf file
    // string confname = read_conf(opt.value(confOption).toStdString(), CONFNAME);

    // // List out available gestures if that is asked for
    // if (args["verbose"] != "")
    // {
    //     if (!opt.isSet(rawOption))
    //     {
    //         cout << "Gestures configured in " << confname << ":" << endl;
    //         for (auto const &handler : handlers)
    //         {
    //             for (auto const &motion : handler.second->Motions())
    //             {
    //                 string _motion, fingers;
    //                 if (typeid(motion.first) == typeid(string))
    //                 {
    //                     _motion = motion.first;
    //                     fingers = "";
    //                 }
    //                 else
    //                 {
    //                     _motion = motion.first;
    //                 }
    //                 cout << handler.second->Name() << " " << _motion << " " << fingers << " " << motion.second << endl;
    //             }
    //         }

    //         if (swipe_min_threshold)
    //             cout << "swipe_threshold " << swipe_min_threshold << endl;
    //         if (timeoutv != DEFAULT_TIMEOUT)
    //             cout << "timeout " << timeoutv << endl;
    //     }

    //     if (opt.isSet(deviceOption))
    //         cout << "device " << opt.value(deviceOption).toStdString() << endl;
    // }

    // // Get touchpad device
    // map<string, string> device = {};
    // if (!opt.isSet(deviceOption) || opt.value(deviceOption).toLower().toStdString() != "all")
    // {
    //     device = get_device(opt.value(deviceOption).toStdString(), cmd_list_devices, opt.value(deviceListOption).toStdString());

    //     if (device.empty())
    //     {
    //         cerr << "Could not determine touchpad device." << endl;
    //         exit(0);
    //     }
    // }
    // if (args["verbose"] != "")
    // {
    //     if (!device.empty())
    //         cout << PROGNAME << ": device " << device["_diag"] << endl;
    //     else
    //         cout << PROGNAME << ": monitoring all devices" << endl;
    // }

    // // If just called to list out above environment info then exit now
    // if (opt.isSet(listOption))
    //     exit(0);

    // // Make sure only one instance running for current user
    // string user = getlogin();
    // FILE *proglock = open_lock({PROGNAME, user});
    // if (proglock == nullptr)
    // {
    //     cerr << PROGNAME << " is already running for " << user << ", terminating .." << endl;
    //     exit(0);
    // }

    // // Set up square of swipe threshold
    // ::abzsquare = pow(swipe_min_threshold, 2);

    // // Note your must "sudo gpasswd -a $USER input" then log out/in for permission to access the device.
    // string devstr = (!device.empty()) ? string(" --device ").append(device["_path"]) : "";
    // string command = string("stdbuf -oL -- ").append(cmd_debug_events).append(devstr);

    // // Sit in a loop forever reading the libinput messages ..
    // GESTURE *handler;
    // //    cmd.stdout
    // for (string line : splitStrings(command))
    // {
    //     // Just output raw messages if in that mode
    //     if (opt.isSet(rawOption))
    //     {
    //         trim(line);
    //         cout << line << endl;
    //         continue;
    //     }

    //     // Only interested in gestures
    //     if (line.find("GESTURE_") == string::npos)
    //         continue;

    //     // Split received message line into relevant fields
    //     vector<string> arr_cmd = splitStrings(line, ' ', 3);
    //     string dev = arr_cmd[0], gevent = arr_cmd[1], time = arr_cmd[2], other = arr_cmd[3];
    //     vector<string> arr_gevent = splitStrings(gevent.substr(8), '_');
    //     string gesture = arr_gevent[0], event = arr_gevent[1];
    //     vector<string> arr_other = splitStrings(other, ' ', 1);
    //     string fingers = arr_other[0], argslist = arr_other[1], params = (argslist != "") ? splitStrings(argslist)[0] : "";

    //     // Action each type of event
    //     if (event == "UPDATE")
    //     {
    //         if (handler)
    //         {
    //             // Split parameters into list of clean numbers
    //             if (!handler->update(resplit(params, "[^-.\d]+")))
    //                 cerr << "Could not parse " << gesture << " " << event << ": " << params << endl;
    //         }
    //     }
    //     else if (event == "BEGIN")
    //     {
    //         handler = handlers[gesture];
    //         if (handler)
    //             handler->begin(fingers);
    //         else
    //             cerr << "Unknown gesture received: " << gesture << "." << endl;
    //     }
    //     else if (event == "END")
    //     {
    //         // Ignore gesture if final action is cancelled
    //         if (handler)
    //         {
    //             if (params != "cancelled")
    //                 handler->end();
    //             handler = nullptr;
    //         }
    //     }
    //     else
    //         cerr << "Unknown gesture + event received: " << gesture << " + " << event << "." << endl;
    // }
    // cout << run("stdbuf -oL -- libinput debug-events --device /dev/input/event17") << endl;

    vector<map<string, string>> device_list = get_devices_list("libinput list-devices", "");
    for(map<string, string> device : device_list) {
        for(auto const &[key, value] : device) {
            cout << key << " : " << value << endl; 
        }
        cout << "=====================================" << endl;
    }

    return a.exec();
}
