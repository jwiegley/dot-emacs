#!/bin/sh
for i in {1..2}; do
montage "screenshot${i}*.png" -mode Concatenate -tile 2x2 -frame 2 -geometry +0+0 -background transparent "montage$i.png";
convert "montage$i.png" -resize 918x "montage$i.png";
done
