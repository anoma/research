#!/bin/bash
for i in *.dvi; do
    ./dvisvgm --font-format=ttf,ah --linkmark=box:Melon $i
done
