BMC = bmc
DREAL = dReal
OPT = 

k10:
	$(BMC) -i -p "[1,2,1,2,1,2,1,2,1,2,1]" -k 10 bouncing_ball_with_drag.drh
	$(DREAL) --precision=0.01 --ode-step=0.01 --ode-grid=16 --visualize bouncing_ball_with_drag_10.smt2

sk10:
	$(BMC) -i -p "[1,2,1,2,1,2,1,2,1,2,1]" -k 10 bouncing_ball_with_drag2.drh
	$(DREAL) $(OPT) --precision=0.09 --ode-step=0.09 --ode-order=10 --visualize \
		bouncing_ball_with_drag2_10.smt2

k20:
	$(BMC) -i -p "[1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1]" -k 20 bouncing_ball_with_drag.drh
	$(DREAL) --precision=0.01 --ode-step=0.01 --ode-grid=16 --visualize bouncing_ball_with_drag_20.smt2

k20-precise:
	$(BMC) -i -p "[1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1]" -k 20 bouncing_ball_with_drag.drh
	$(DREAL) --precision=0.001 --ode-step=0.01 --ode-grid=16 --visualize bouncing_ball_with_drag_20.smt2

k20-smallstep:
	$(BMC) -i -p "[1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1]" -k 20 bouncing_ball_with_drag.drh
	$(DREAL) --precision=0.01 --ode-step=0.001 --ode-grid=16 --visualize bouncing_ball_with_drag_20.smt2

k20-ps:
	$(BMC) -i -p "[1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1]" -k 20 bouncing_ball_with_drag.drh
	$(DREAL) --precision=0.001 --ode-step=0.001 --ode-grid=16 --visualize bouncing_ball_with_drag_20.smt2

k40:
	$(BMC) -i -p "[1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1]" -k 40 bouncing_ball_with_drag.drh
	$(DREAL) --precision=0.01 --ode-step=0.01 --ode-grid=16 --visualize bouncing_ball_with_drag_40.smt2

k40-precise:
	$(BMC) -i -p "[1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1]" -k 40 bouncing_ball_with_drag.drh
	$(DREAL) --precision=0.001 --ode-step=0.01 --ode-grid=16 --visualize bouncing_ball_with_drag_40.smt2

k40-smallstep:
	$(BMC) -i -p "[1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1]" -k 40 bouncing_ball_with_drag.drh
	$(DREAL) --precision=0.01 --ode-step=0.001 --ode-grid=16 --visualize bouncing_ball_with_drag_40.smt2

k40-ps:
	$(BMC) -i -p "[1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1]" -k 40 bouncing_ball_with_drag.drh
	$(DREAL) --precision=0.001 --ode-step=0.001 --ode-grid=16 --visualize bouncing_ball_with_drag_40.smt2

clean:
	rm -f *.preprocessed.drh
	rm -f *.smt2
	rm -f *.json
	rm -f *.proof

