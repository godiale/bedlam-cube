cube: cube.cpp
	g++ --std=c++0x -O3 -o cube -pthread cube.cpp

all: cube

