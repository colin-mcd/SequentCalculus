GHCFLAGS=-Wall -Wno-unused-matches -Wno-unused-local-binds -Wno-missing-signatures -Wno-name-shadowing -Wno-orphans -Wno-type-defaults -Wno-unused-matches -Wno-incomplete-patterns

all: CutElim.exe

CutElim.exe: *.hs
	mkdir -p .objects
	ghc Main.hs --make -odir .objects -hidir .objects -o CutElim.exe $(GHCFLAGS)

clean:
	rm -f *.o *.hi *.exe .objects/*.o .objects/*.hi
