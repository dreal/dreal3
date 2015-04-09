DREACH = ../../../bin/dReach
OPT =

k2:
	$(DREACH) -k 2 scaled_prostate_infix.drh --precision=0.005 --visualize $(OPT)

k2-precise:
	$(DREACH) -k 2 scaled_prostate_infix.drh --precision=0.002 --visualize $(OPT)

full:
	$(DREACH) -k 6 scaled_prostate_infix_full.drh --precision=0.005 --visualize $(OPT)

clean:
	rm -f *.preprocessed.drh
	rm -f *.smt2
	rm -f *.json
	rm -f *.proof
