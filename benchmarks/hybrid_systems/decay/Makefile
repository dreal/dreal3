BMC = bmc
DREAL = dReal

decay1:
	$(BMC) -k 2 -p "[1,2,3]" -i decay_1.drh
	$(DREAL) --precision=0.1 --ode-step=0.05  --ode-grid=32 --visualize decay_1_2.smt2

decay2:
	$(BMC) -k 1 -p "[1,2]" -i decay_2_new.drh
	$(DREAL) --precision=0.1 --ode-step=0.05  --ode-grid=32 --visualize decay_2_new_1.smt2

decay-un:
	$(BMC) -k 1 -p "[1,2]" -i decay-un_new.drh
	$(DREAL) --precision=0.1 --ode-step=0.05  --ode-grid=32 --visualize \
		decay-un_new_1.smt2

clean:
	rm *.preprocessed.drh
	rm *.smt2
	rm *.json

