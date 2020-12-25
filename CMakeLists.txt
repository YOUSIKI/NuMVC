cmake_minimum_required(VERSION 3.17)
project(NuMVC)

set(CMAKE_CXX_STANDARD 14)

set(CMAKE_CXX_FLAGS "-Wall -Wextra")
#set(CMAKE_CXX_FLAGS_DEBUG "-g")
set(CMAKE_CXX_FLAGS_DEBUG "-O3")
set(CMAKE_CXX_FLAGS_RELEASE "-O3")

add_executable(NuMVC numvc.cpp)
add_executable(EWLS ewls.cpp)
