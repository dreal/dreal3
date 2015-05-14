DREACH = dReach
OPT =
good:
	$(DREACH) -k 3 cardiac_good.drh --precision 0.001 --visualize $(OPT)

bad:
	$(DREACH) -k 3 cardiac_bad.drh --precision 0.001 --visualize $(OPT)

to1_good:
	$(DREACH) -k 3 cardiac_to1_good.drh --precision 0.001 --visualize $(OPT)

to1_bad:
	$(DREACH) -k 3 cardiac_to1_bad.drh --precision 0.001 --visualize $(OPT)

to2_good:
	$(DREACH) -k 3 cardiac_to2_good.drh --precision 0.01 --visualize $(OPT)

to2_bad:
	$(DREACH) -k 3 cardiac_to2_bad.drh --precision 0.001 --visualize $(OPT)

tso1_tso2_bad:
	$(DREACH) -k 3 cardiac_tso1_tso2_bad.drh --precision 0.001 --visualize $(OPT)

clean:
	rm -f *.preprocessed.drh
	rm -f *.smt2
	rm -f *.json
	rm -f *.proof
	rm -f *.output
