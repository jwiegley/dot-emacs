ECUKES = $(shell find elpa/ecukes-*/ecukes | tail -1)

all:
	carton exec ${ECUKES} features
