BMC = ../../../tools/bmc/bmc.sh
DREAL = dreal

k2:
	bmc -k 2 -p "[1,2,3]" -i 3mode_3d_oscillator.drh
	dReal --precision=0.01 --ode-step=0.01 --ode-grid=32 --visualize 3mode_3d_oscillator_2.smt2

k2-smallstep:
	bmc -k 2 -p "[1,2,3]" -i 3mode_3d_oscillator.drh
	dReal --precision=0.01 --ode-step=0.005 --ode-grid=32 --visualize 3mode_3d_oscillator_2.smt2

k2-precise:
	bmc -k 2 -p "[1,2,3]" -i 3mode_3d_oscillator.drh
	dReal --precision=0.005 --ode-step=0.01 --ode-grid=32 --visualize 3mode_3d_oscillator_2.smt2

k2-ps:
	bmc -k 2 -p "[1,2,3]" -i 3mode_3d_oscillator.drh
	dReal --precision=0.005 --ode-step=0.005 --ode-grid=32 --visualize 3mode_3d_oscillator_2.smt2

k3:
	bmc -k 3 -p "[1,2,3,1]" -i 3mode_3d_oscillator.drh
	dReal --precision=0.01 --ode-step=0.01 --ode-grid=32 --visualize 3mode_3d_oscillator_3.smt2
k5:
	bmc -k 5 -p "[1,2,3,1,2,3]" -i 3mode_3d_oscillator.drh
	dReal --precision=0.01 --ode-step=0.01 --ode-grid=32 --visualize 3mode_3d_oscillator_5.smt2

k11:
	bmc -k 11 -p "[1,2,3,1,2,3,1,2,3,1,2,3]" -i 3mode_3d_oscillator.drh
	dReal --precision=0.01 --ode-step=0.01 --ode-grid=32 --visualize \
		3mode_3d_oscillator_11.smt2

clean:
	rm *.preprocessed.drh
	rm *.smt2
	rm *.json
