BMC = ../../../tools/simple-bmc/bmc.sh
DREAL = dReal
OPT =

k3:
	$(BMC) -k 3 new_cardiac_stim.drh
	$(DREAL) --precision=0.001 $(OPT) --visualize new_cardiac_stim_3_0.smt2

k7:
	$(BMC) -k 7 new_cardiac_8m.drh
	$(DREAL) --precision=0.001 $(OPT) --visualize new_cardiac_8m_7_0.smt2

k23:
	$(BMC) -k 23 new_cardiac_8m.drh
	$(DREAL) --precision=0.005 $(OPT) --visualize new_cardiac_8m_23_0.smt2

k31:
	$(BMC) -k 31 new_cardiac_8m.drh
	$(DREAL) --precision=0.001 --visualize new_cardiac_8m_31_0.smt2

k47:
	$(BMC) -k 47 new_cardiac_8m.drh
	$(DREAL) --precision=0.001 --visualize new_cardiac_8m_47_0.smt2

k55:
	$(BMC) -k 55 new_cardiac_8m.drh
	$(DREAL) --precision=0.001 --visualize new_cardiac_8m_55_0.smt2

clean:
	rm -f *.preprocessed.drh
	rm -f *.smt2
	rm -f *.json
	rm -f *.proof
