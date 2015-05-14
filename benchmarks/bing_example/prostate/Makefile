DREACH = dReach
OPT =

h1:
	$(DREACH) -k 2 prostate_h1.drh --precision 0.009 --visualize $(OPT)

h2:
	$(DREACH) -k 2 prostate_h2.drh --precision 0.005 --visualize $(OPT)

h3:
	$(DREACH) -k 5 prostate_h3.drh --precision 0.005 --visualize $(OPT)

h1_free:
	$(DREACH) -k 2 prostate_h1_free.drh --precision 0.005 --visualize $(OPT)

h2_free:
	$(DREACH) -k 2 prostate_h2_free.drh --precision 0.005 --visualize $(OPT)

h3_free:
	$(DREACH) -k 5 prostate_h3_free.drh --precision 0.005 --visualize $(OPT)

p8:
	$(DREACH) -k 5 prostate_p8.drh --precision 0.005 --visualize $(OPT)

p10:
	$(DREACH) -k 4 prostate_p10.drh --precision 0.005 --visualize $(OPT)

p45:
	$(DREACH) -k 2 prostate_p45.drh --precision 0.005 --visualize $(OPT)

p97:
	$(DREACH) -k 5 prostate_p97.drh --precision 0.005 --visualize $(OPT)

p8_opt:
	$(DREACH) -k 5 prostate_p8_opt.drh --precision 0.005 --visualize $(OPT)

p10_opt:
	$(DREACH) -k 4 prostate_p10_opt.drh --precision 0.005 --visualize $(OPT)

p45_opt:
	$(DREACH) -k 2 prostate_p45_opt.drh --precision 0.005 --visualize $(OPT)

p97_opt:
	$(DREACH) -k 5 prostate_p97_opt.drh --precision 0.005 --visualize $(OPT)

clean:
	rm -f *.preprocessed.drh
	rm -f *.smt2
	rm -f *.json
	rm -f *.proof
	rm -f *.output
