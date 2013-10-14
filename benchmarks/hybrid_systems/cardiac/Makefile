BMC = bmc
DREAL = dReal
DREAL_OPT = 

k3:
	$(BMC) -k 3 -p "[1,2,3,4]" -i new_cardiac_stim.drh
	$(DREAL) --precision=0.001 --ode-step=0.01 --ode-grid=32 $(DREAL_OPT) --visualize new_cardiac_stim_3.smt2

k7:
	$(BMC) -k 7 -p "[1,2,3,4,5,6,7,8]" -i new_cardiac_8m.drh
	$(DREAL) --precision=0.001 --ode-step=0.001 --ode-grid=128 $(DREAL_OPT) --visualize new_cardiac_8m_7.smt2

k23:
	$(BMC) -k 23 -p "[1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8]" -i new_cardiac_8m.drh
	$(DREAL) --precision=0.001 --ode-step=0.001 --ode-grid=128 --visualize new_cardiac_8m_23.smt2

k31:
	$(BMC) -k 31 -p "[1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8]" -i new_cardiac_8m.drh
	$(DREAL) --precision=0.001 --ode-step=0.01 --ode-grid=32 --visualize new_cardiac_8m_31.smt2

k47:
	$(BMC) -k 47 -p "[1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8]" -i new_cardiac_8m.drh
	$(DREAL) --precision=0.001 --ode-step=0.01 --ode-grid=32 --visualize new_cardiac_8m_47.smt2

k55:
	$(BMC) -k 55 -p "[1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8]" -i new_cardiac_8m.drh
	$(DREAL) --precision=0.001 --ode-step=0.01 --ode-grid=32 --visualize new_cardiac_8m_55.smt2

clean:
	rm -f *.preprocessed.drh
	rm -f *.smt2
	rm -f *.json
	rm -f *.proof

