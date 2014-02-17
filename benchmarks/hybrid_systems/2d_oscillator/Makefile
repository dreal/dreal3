BMC = ../../../tools/bmc/bmc.sh
DREAL = dreal

k2:
	$(BMC) -k 2 3mode_3d_oscillator.drh
	dReal --precision=0.01 --ode-step=0.01 --ode-grid=32 --visualize 3mode_3d_oscillator_2_0.smt2

k2-smallstep:
	$(BMC) -k 2 -p "[1,2,3]" -i 3mode_3d_oscillator.drh
	dReal --precision=0.01 --ode-step=0.005 --ode-grid=32 --visualize 3mode_3d_oscillator_2.smt2

k2-precise:
	$(BMC) -k 2 -p "[1,2,3]" -i 3mode_3d_oscillator.drh
	dReal --precision=0.005 --ode-step=0.01 --ode-grid=32 --visualize 3mode_3d_oscillator_2.smt2

k2-ps:
	bmc -k 2 -p "[1,2,3]" -i 3mode_3d_oscillator.drh
	dReal --precision=0.005 --ode-step=0.005 --ode-grid=32 --visualize 3mode_3d_oscillator_2.smt2

k3:
	$(BMC) -k 3 -p "[1,2,3,1]" -i 3mode_3d_oscillator.drh
	dReal --precision=0.01 --ode-step=0.01 --ode-grid=32 --visualize 3mode_3d_oscillator_3.smt2
k5:
	$(BMC) -k 5 3mode_3d_oscillator.drh
	dReal --precision=0.01 --ode-step=0.01 --ode-grid=32 --visualize 3mode_3d_oscillator_5_0.smt2

k11:
	$(BMC) -k 11 3mode_3d_oscillator.drh
	dReal --precision=0.01 --ode-step=0.01 --ode-grid=32 --visualize \
		3mode_3d_oscillator_11_0.smt2

clean:
	rm *.preprocessed.drh
	rm *.smt2
	rm *.json
