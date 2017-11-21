
gen-discover:
	## This obviously depends on assess being available and in the
	## right location
	cp ../../assess/assess-discover.el .
	perl -i -pe 's/assess-discover/fudge-discover/g' assess-discover.el
	mv assess-discover.el fudge-discover.el
