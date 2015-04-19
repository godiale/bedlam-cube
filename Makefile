cube: cube.cpp
	g++ --std=c++0x -Wall -O3 -o cube -pthread cube.cpp

all: cube

