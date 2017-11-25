#!/usr/bin/env sh
for i in $(seq 0 15 359); do
    convert refman/icon/rooster-light.png -gravity center -background transparent \
            -rotate $i -extent 64x64 +repage refman/icon/rooster-light-$i.png
    convert refman/icon/rooster-dark.png -gravity center -background transparent \
            -rotate $i -extent 64x64 +repage refman/icon/rooster-dark-$i.png
done
