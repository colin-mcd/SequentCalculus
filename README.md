### Sequent Calculus

Currently, this repo just stores an implementation of the cut-elimination theorem for Buss' version of PK.

To build:
```bash
make
```

Then to run the program:
```bash
cat sample_proof.txt | ./CutElim.exe | tex/tex2pdf.sh
```
And it will write a nice LaTeX proof in `cut-free-proof.tex`.
