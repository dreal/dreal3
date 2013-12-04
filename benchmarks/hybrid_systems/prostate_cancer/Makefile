BMC = ../../../tools/bmc/bmc.sh
DREAL = dReal

k2:
	$(BMC) -i -k 2 -p "[2,1,2]" scaled_prostate_infix.drh
	$(DREAL) --precision=0.005 --ode-step=0.001 --ode-grid=16 --visualize scaled_prostate_infix_2.smt2

k2-precise:
	$(BMC) -i -k 2 -p "[2,1,2]" scaled_prostate_infix.drh
	$(DREAL) --precision=0.002 --ode-step=0.001 --ode-grid=16 --visualize scaled_prostate_infix_2.smt2

full:
	$(BMC) -i -k 6 -p "[2,1,2,1,2,1,2]" scaled_prostate_infix_full.drh
	$(DREAL) --precision=0.002 --ode-step=0.001 --ode-grid=16 --visualize scaled_prostate_infix_full_6.smt2

clean:
	rm -f *.preprocessed.drh
	rm -f *.smt2
	rm -f *.json
	rm -f *.proof
