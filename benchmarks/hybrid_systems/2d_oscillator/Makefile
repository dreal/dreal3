BMC = bmc
DREAL = dreal

all:
	bmc -k 0 -p "[1]" -i 2d_oscillator.drh
	dReal --precision=0.001 --ode-step=0.01 --ode-grid=32 --visualize 2d_oscillator_0.smt2

clean:
	rm *.preprocessed.drh
	rm *.smt2
	rm *.json

