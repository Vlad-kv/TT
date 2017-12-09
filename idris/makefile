.PHONY: build_and_run

build_and_run: first.exe
	first.exe

first.exe: first.idr
	idris first.idr -o first.exe

clean:
	del *.exe *.ibc
