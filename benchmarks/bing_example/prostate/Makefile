BMC = ../../../tools/bmc/bmc.sh
DREAL= dReal
OPT =

h1:
	$(BMC) -k 2 prostate_h1.drh
	time find . -name "prostate_h1_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.009 --visualize $(OPT) {} ";"

h2:
	$(BMC) -k 2 prostate_h2.drh
	time find . -name "prostate_h2_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.005 --visualize $(OPT) {} ";"

h3:
	$(BMC) -k 5 prostate_h3.drh
	time find . -name "prostate_h3_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.005 --visualize $(OPT) {} ";"

h1_free:
	$(BMC) -k 2 prostate_h1_free.drh
	time find . -name "prostate_h1_free_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.005 --visualize $(OPT) {} ";"

h2_free:
	$(BMC) -k 2 prostate_h2_free.drh
	time find . -name "prostate_h2_free_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.005 --visualize $(OPT) {} ";"

h3_free:
	$(BMC) -k 5 prostate_h3_free.drh
	time find . -name "prostate_h3_free_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.005 --visualize $(OPT) {} ";"

p8:
	$(BMC) -k 5 prostate_p8.drh
	time find . -name "prostate_p8_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.005 --visualize $(OPT) {} ";"

p10:
	$(BMC) -k 4 prostate_p10.drh
	time find . -name "prostate_p10_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.005 --visualize $(OPT) {} ";"

p45:
	$(BMC) -k 2 prostate_p45.drh
	time find . -name "prostate_p45_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.005 --visualize $(OPT) {} ";"

p97:
	$(BMC) -k 5 prostate_p97.drh
	time find . -name "prostate_p97_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.005 --visualize $(OPT) {} ";"

p8_opt:
	$(BMC) -k 5 prostate_p8_opt.drh
	time find . -name "prostate_p8_opt_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.005 --visualize $(OPT) {} ";"

p10_opt:
	$(BMC) -k 4 prostate_p10_opt.drh
	time find . -name "prostate_p10_opt_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.005 --visualize $(OPT) {} ";"

p45_opt:
	$(BMC) -k 2 prostate_p45_opt.drh
	time find . -name "prostate_p45_opt_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.005 --visualize $(OPT) {} ";"

p97_opt:
	$(BMC) -k 5 prostate_p97_opt.drh
	time find . -name "prostate_p97_opt*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.005 --visualize $(OPT) {} ";"

clean:
	rm -f *.preprocessed.drh
	rm -f *.smt2
	rm -f *.json
	rm -f *.proof
