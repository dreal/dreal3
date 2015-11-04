DREACH = ../../../bin/dReach
OPT =

k3:
	$(DREACH) -k 3 new_cardiac_stim.drh --precision 0.001 --visualize $(OPT)

k7:
	$(DREACH) -k 7 new_cardiac_8m.drh --precision 0.001 --visualize  $(OPT)

k23:
	$(DREACH) -l 23 -k 23 new_cardiac_8m.drh --precision 0.005 --visualize $(OPT)

k31:
	$(DREACH) -l 31 -k 31 new_cardiac_8m.drh --precision 0.001 --visualize $(OPT)

k47:
	$(DREACH) -l 47 -k 47 new_cardiac_8m.drh --precision 0.001 --visualize $(OPT)

k55:
	$(DREACH) -l 55 -k 55 new_cardiac_8m.drh --precision 0.001 --visualize $(OPT)

clean:
	rm -f *.preprocessed.drh
	rm -f *.smt2
	rm -f *.json
	rm -f *.proof
	rm -f *.output
