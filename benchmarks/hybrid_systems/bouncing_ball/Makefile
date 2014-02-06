BMC = ../../../tools/simple-bmc/bmc.sh
DREAL = dReal
OPT =

g2:
	$(BMC)  -k 2 bouncing_ball_with_drag_g.drh
	$(DREAL) --precision=0.01 --ode-grid=1024 --visualize $(OPT) bouncing_ball_with_drag_g_2.smt2

k2:
	$(BMC)  -k 2 bouncing_ball_with_drag.drh
	$(DREAL) --precision=0.01 --ode-grid=1024 --visualize $(OPT) bouncing_ball_with_drag_2_0.smt2

k4:
	$(BMC)  -k 4 bouncing_ball_with_drag.drh
	$(DREAL) --precision=0.001 --ode-grid=1024 --visualize $(OPT) bouncing_ball_with_drag_4.smt2

k10:
	$(BMC)  -k 10 bouncing_ball_with_drag.drh
	$(DREAL) --precision=0.01 --ode-grid=1024 --visualize bouncing_ball_with_drag_10_0.smt2

sk10:
	$(BMC)  -p "[1,2,1,2,1,2,1,2,1,2,1]" -k 10 bouncing_ball_with_drag2.drh
	$(DREAL) $(OPT) --precision=0.09 --ode-step=0.09 --ode-order=10 --visualize \
		bouncing_ball_with_drag2_10.smt2

k20:
	$(BMC)  -k 20 bouncing_ball_with_drag.drh
	$(DREAL) --precision=0.01 --ode-grid=1024 --visualize bouncing_ball_with_drag_20_0.smt2

k20-precise:
	$(BMC)  -p "[1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1]" -k 20 bouncing_ball_with_drag.drh
	$(DREAL) --precision=0.001 --ode-step=0.01 --ode-grid=16 --visualize bouncing_ball_with_drag_20.smt2

k20-smallstep:
	$(BMC)  -p "[1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1]" -k 20 bouncing_ball_with_drag.drh
	$(DREAL) --precision=0.01 --ode-step=0.001 --ode-grid=16 --visualize bouncing_ball_with_drag_20.smt2

k20-ps:
	$(BMC)  -p "[1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1]" -k 20 bouncing_ball_with_drag.drh
	$(DREAL) --precision=0.001 --ode-step=0.001 --ode-grid=16 --visualize bouncing_ball_with_drag_20.smt2

k40:
	$(BMC)  -p "[1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1]" -k 40 bouncing_ball_with_drag.drh
	$(DREAL) --precision=0.01 --ode-step=0.01 --ode-grid=16 --visualize bouncing_ball_with_drag_40.smt2

k40-precise:
	$(BMC)  -p "[1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1]" -k 40 bouncing_ball_with_drag.drh
	$(DREAL) --precision=0.001 --ode-step=0.01 --ode-grid=16 --visualize bouncing_ball_with_drag_40.smt2

k40-smallstep:
	$(BMC)  -p "[1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1]" -k 40 bouncing_ball_with_drag.drh
	$(DREAL) --precision=0.01 --ode-step=0.001 --ode-grid=16 --visualize bouncing_ball_with_drag_40.smt2

k40-ps:
	$(BMC)  -p "[1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1]" -k 40 bouncing_ball_with_drag.drh
	$(DREAL) --precision=0.001 --ode-step=0.001 --ode-grid=16 --visualize bouncing_ball_with_drag_40.smt2

clean:
	rm -f *.preprocessed.drh
	rm -f *.smt2
	rm -f *.json
	rm -f *.proof
