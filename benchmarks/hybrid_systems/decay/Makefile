BMC = bmc
DREAL = dReal

all:
	$(BMC) -k 2 -p "[1,2,3]" -i decay_1.drh
	$(DREAL) --precision=0.1  --ode-grid=32 --visualize decay_1_2.smt2

clean:
	rm *.preprocessed.drh
	rm *.smt2
	rm *.json

