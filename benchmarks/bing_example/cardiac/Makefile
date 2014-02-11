BMC = ../../../tools/simple-bmc/bmc.sh
DREAL= dReal
OPT =
good:
	$(BMC) -k 3 cardiac_good.drh
	find . -name "cardiac_good_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.001 --visualize $(OPT) {} ";"

bad:
	$(BMC) -k 3 cardiac_bad.drh
	find . -name "cardiac_bad_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.001 --visualize $(OPT) {} ";"

to1_good:
	$(BMC) -k 3 cardiac_to1_good.drh
	find . -name "cardiac_to1_good_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.001 --visualize $(OPT) {} ";"

to1_bad:
	$(BMC) -k 3 cardiac_to1_bad.drh
	find . -name "cardiac_to1_bad_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.001 --visualize $(OPT) {} ";"

to2_good:
	$(BMC) -k 3 cardiac_to2_good.drh
	find . -name "cardiac_to2_good_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.01 --visualize $(OPT) {} ";"

to2_bad:
	$(BMC) -k 3 cardiac_to2_bad.drh
	find . -name "cardiac_to2_bad_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.001 --visualize $(OPT) {} ";"

tso1_tso2_bad:
	$(BMC) -k 3 cardiac_tso1_tso2_bad.drh
	find . -name "cardiac_tso1_tso2_bad_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.001 --visualize $(OPT) {} ";"

clean:
	rm -f *.preprocessed.drh
	rm -f *.smt2
	rm -f *.json
	rm -f *.proof
