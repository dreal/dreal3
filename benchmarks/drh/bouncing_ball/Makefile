DREACH = ../../../bin/dReach
OPT =

simple:
	$(DREACH) -k 3 bouncing_ball.drh --precision 0.01 --ode_grid 1024 --visualize $(OPT)

k2:
	$(DREACH) -k 2 bouncing_ball_with_drag.drh --precision 0.01 --ode_grid 1024 --visualize $(OPT)

k4:
	$(DREACH) -k 4 bouncing_ball_with_drag.drh --precision 0.001 --ode_grid 1024 --visualize $(OPT)

k10:
	$(DREACH) -k 10 bouncing_ball_with_drag.drh $(OPT)

sk10:
	$(DREACH) -k 10 bouncing_ball_with_drag2.drh --precision 0.09 --ode_step 0.09 --ode_order 10 --visualize $(OPT)

k20:
	$(DREACH) -k 20 bouncing_ball_with_drag.drh --precision 0.01 --ode_grid 1024 --visualize $(OPT)

k20-precise:
	$(DREACH) -k 20 bouncing_ball_with_drag.drh --precision 0.001 --ode_step 0.01 --ode_grid 16 --visualize $(OPT)

k20-smallstep:
	$(DREACH) -k 20 bouncing_ball_with_drag.drh --precision 0.01 --ode_step 0.001 --ode_grid 16 --visualize $(OPT)

k20-ps:
	$(DREACH) -k 20 bouncing_ball_with_drag.drh --precision 0.001 --ode_step 0.001 --ode_grid 16 --visualize $(OPT)

k40:
	$(DREACH) -k 40 bouncing_ball_with_drag.drh --precision 0.01 --ode_step 0.01 --ode_grid 16 --visualize $(OPT)

k40-precise:
	$(DREACH) -k 40 bouncing_ball_with_drag.drh --precision 0.001 --ode_step 0.01 --ode_grid 16 --visualize $(OPT)

k40-smallstep:
	$(DREACH) -k 40 bouncing_ball_with_drag.drh --precision 0.01 --ode_step 0.001 --ode_grid 16 --visualize $(OPT)

k40-ps:
	$(DREACH) -k 40 bouncing_ball_with_drag.drh --precision 0.001 --ode_step 0.001 --ode_grid 16 --visualize $(OPT)

clean:
	rm -f *.preprocessed.drh
	rm -f *.smt2
	rm -f *.json
	rm -f *.proof
	rm -f *.output
