DREACH = ../../../bin/dReach
OPT =

k2:
	$(DREACH) -k 2 3mode_3d_oscillator.drh  --precision 0.01 --ode_step 0.01 --ode_grid 32 --visualize $(OPT)

k2-smallstep:
	$(DREACH) -k 2 3mode_3d_oscillator.drh --precision 0.01 --ode_step 0.005 --ode_grid 32 --visualize $(OPT)

k2-precise:
	$(DREACH) -k 2 3mode_3d_oscillator.drh --precision 0.005 --ode_step 0.01 --ode_grid 32 --visualize $(OPT)

k2-ps:
	$(DREACH) -k 2 3mode_3d_oscillator.drh --precision 0.005 --ode_step 0.005 --ode_grid 32 --visualize $(OPT)

k3:
	$(DREACH) -k 3 3mode_3d_oscillator.drh --precision 0.01 --ode_step 0.01 --ode_grid 32 --visualize $(OPT)
k5:
	$(DREACH) -k 5 3mode_3d_oscillator.drh --precision 0.01 --ode_grid 32 --visualize $(OPT)

k11:
	$(DREACH) -k 11 3mode_3d_oscillator.drh --precision 0.01 --ode_grid 32 --visualize $(OPT)

clean:
	rm *.preprocessed.drh
	rm *.smt2
	rm *.json
	rm *.output
