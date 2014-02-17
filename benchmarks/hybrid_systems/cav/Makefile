BMC = ../../../tools/bmc/bmc.sh
INV = ../../../tools/invariant-checking/inv.sh
DREAL = dReal
OPT =

flowstar:
	$(BMC) -k 1 flowstar1.drh
	$(DREAL) --precision=0.0001 $(OPT) --visualize --proof flowstar1_1_0.smt2

robot:
	$(INV) robot.drh
	$(DREAL) --precision=0.001 $(OPT) --visualize --proof robot_ind.smt2

clean:
	rm -f *.preprocessed.drh
	rm -f *.smt2
	rm -f *.json
	rm -f *.proof
