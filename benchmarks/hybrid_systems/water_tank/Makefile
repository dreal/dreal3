BMC = ../../../tools/bmc/bmc.sh
DREAL = dreal

k1:
	bmc -k 1 -p "[1,2]" -i nonlinear_watertank.drh
	dReal --precision=0.01 --ode-step=0.01 --ode-grid=32 --visualize nonlinear_watertank_1.smt2

k3:
	bmc -k3 -p "[1,2,1,2]" -i nonlinear_watertank.drh
	dReal --precision=0.01 --ode-step=0.01 --ode-grid=32 --visualize nonlinear_watertank_3.smt2

k5:
	bmc -k 5 -p "[1,2,1,2,1,2]" -i nonlinear_watertank.drh
	dReal --precision=0.001 --ode-step=0.001 --proof --ode-grid=32 --visualize nonlinear_watertank_5.smt2

clean:
	rm *.preprocessed.drh
	rm *.smt2
	rm *.json
