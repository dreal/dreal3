BMC = ../../../tools/simple-bmc/bmc.sh
DREAL = dReal

k2:
	$(BMC) -k 2  scaled_prostate_infix.drh
	$(DREAL) --precision=0.005 --visualize scaled_prostate_infix_2_0.smt2

k2-precise:
	$(BMC) -k 2 scaled_prostate_infix.drh
	$(DREAL) --precision=0.002 --visualize scaled_prostate_infix_2_0.smt2

full:
	$(BMC) -k 6 scaled_prostate_infix_full.drh
	$(DREAL) --precision=0.005 --visualize scaled_prostate_infix_full_6_0.smt2

clean:
	rm -f *.preprocessed.drh
	rm -f *.smt2
	rm -f *.json
	rm -f *.proof
