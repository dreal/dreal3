BMC = bmc
DREAL = dReal
DREAL_OPT = --verbose

all:
	$(BMC) -k 7 -p "[1,2,3,4,5,6,7,8]" -i new_cardiac_8m.drh
	$(DREAL) --precision=0.001 --ode-step=0.01 --ode-grid=32 $(DREAL_OPT) --visualize new_cardiac_8m_7.smt2

full:
	$(BMC) -k 23 -p "[1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8]" -i new_cardiac_8m.drh
	$(DREAL) --precision=0.001 --ode-step=0.01 --ode-grid=32 --visualize new_cardiac_8m_23.smt2

clean:
	rm -f *.preprocessed.drh
	rm -f *.smt2
	rm -f *.json
	rm -f *.proof

