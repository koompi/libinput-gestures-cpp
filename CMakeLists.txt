cmake_minimum_required(VERSION 3.14)

project(custom-libinput-gestures LANGUAGES CXX)

set(CMAKE_INCLUDE_CURRENT_DIR ON)

set(CMAKE_AUTOUIC ON)
set(CMAKE_AUTOMOC ON)
set(CMAKE_AUTORCC ON)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

find_package(Qt5Core)

add_executable(custom-libinput-gestures
  globals.h
  globals.cpp
  main.cpp
)
target_link_libraries(custom-libinput-gestures Qt${QT_VERSION_MAJOR}::Core)
