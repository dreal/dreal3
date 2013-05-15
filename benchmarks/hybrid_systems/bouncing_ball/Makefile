BMC = bmc
DREAL = dReal

path:
	$(BMC) -i -p "[1,2,1,2,1,2,1,2,1,2,1]" -k 10 bouncing_ball_with_drag.drh
	$(DREAL) --verbose --precision=0.01 --ode-step=0.01 --ode-grid=16 --visualize bouncing_ball_with_drag_10.smt2

no-path:
	$(BMC) -i -k 10 bouncing_ball_with_drag.drh
	$(DREAL) --verbose --precision=0.01 --ode-step=0.01 --ode-grid=16 --visualize bouncing_ball_with_drag_10.smt2

clean:
	rm -f *.preprocessed.drh
	rm -f *.smt2
	rm -f *.json
	rm -f *.proof

