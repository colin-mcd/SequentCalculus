#!/usr/bin/env bash

# The following line taken from https://stackoverflow.com/a/246128
SCRIPT_DIR=$(cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd)

cd $SCRIPT_DIR

cat preamble.tex > proof.tex
cat >> proof.tex
cat postamble.tex >> proof.tex

pdflatex proof.tex && rm proof.tex proof.log proof.aux && evince proof.pdf &

