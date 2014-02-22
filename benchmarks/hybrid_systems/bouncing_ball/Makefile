DREACH = dReach
OPT =

k2:
	$(DREACH) -k 2 bouncing_ball_with_drag.drh --precision=0.01 --ode-grid=1024 --visualize $(OPT)

k4:
	$(DREACH) -k 4 bouncing_ball_with_drag.drh --precision=0.001 --ode-grid=1024 --visualize $(OPT)

k10:
	$(DREACH) -k 10 bouncing_ball_with_drag.drh --precision=0.01 --ode-grid=1024 --visualize $(OPT)

sk10:
	$(DREACH) -k 10 bouncing_ball_with_drag2.drh --precision=0.09 --ode-step=0.09 --ode-order=10 --visualize $(OPT)

k20:
	$(DREACH) -k 20 bouncing_ball_with_drag.drh --precision=0.01 --ode-grid=1024 --visualize $(OPT)

k20-precise:
	$(DREACH) -k 20 bouncing_ball_with_drag.drh --precision=0.001 --ode-step=0.01 --ode-grid=16 --visualize $(OPT)

k20-smallstep:
	$(DREACH) -k 20 bouncing_ball_with_drag.drh --precision=0.01 --ode-step=0.001 --ode-grid=16 --visualize $(OPT)

k20-ps:
	$(DREACH) -k 20 bouncing_ball_with_drag.drh --precision=0.001 --ode-step=0.001 --ode-grid=16 --visualize $(OPT)

k40:
	$(DREACH) -k 40 bouncing_ball_with_drag.drh --precision=0.01 --ode-step=0.01 --ode-grid=16 --visualize $(OPT)

k40-precise:
	$(DREACH) -k 40 bouncing_ball_with_drag.drh --precision=0.001 --ode-step=0.01 --ode-grid=16 --visualize $(OPT)

k40-smallstep:
	$(DREACH) -k 40 bouncing_ball_with_drag.drh --precision=0.01 --ode-step=0.001 --ode-grid=16 --visualize $(OPT)

k40-ps:
	$(DREACH) -k 40 bouncing_ball_with_drag.drh --precision=0.001 --ode-step=0.001 --ode-grid=16 --visualize $(OPT)

clean:
	rm -f *.preprocessed.drh
	rm -f *.smt2
	rm -f *.json
	rm -f *.proof
	rm -f *.output
