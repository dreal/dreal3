BMC = bmc
DREAL = dreal

k0:
	bmc -k 0 -p "[1]" -i 3mode_3d_oscillator.drh
	dReal --precision=0.01 --ode-step=0.01 --ode-grid=32 --visualize 3mode_3d_oscillator_0.smt2

k2:
	bmc -k 2 -p "[1,2,3]" -i 3mode_3d_oscillator.drh
	dReal --precision=0.01 --ode-step=0.01 --ode-grid=32 --visualize 3mode_3d_oscillator_2.smt2

clean:
	rm *.preprocessed.drh
	rm *.smt2
	rm *.json

