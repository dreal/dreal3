BMC = ../../../tools/bmc/bmc.sh
DREAL = dReal
OPT =

k0:
	$(BMC) -k 0 quad0.drh
	time find . -name "quad0_0_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.01 --visualize $(OPT) {} ";"
	cp quad0_0_0.smt2.json ~/work/dReal/tools/ODE_visualization/data.json

k1:
	$(BMC) -k 1 quad1.drh
	time find . -name "quad1_1_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.01 --ode-grid=1024 --visualize $(OPT) {} ";"
	cp quad1_1_0.smt2.json ~/work/dReal/tools/ODE_visualization/data.json

k2:
	$(BMC) -k 2 quad2.drh
	time find . -name "quad2_2_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.01 --ode-grid=1024 --visualize $(OPT) {} ";"
	cp quad2_2_0.smt2.json ~/work/dReal/tools/ODE_visualization/data.json

k2-1:
	$(BMC) -k 2 quad2-1.drh
	time find . -name "quad2-1_2_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.01 --ode-grid=1024 --visualize $(OPT) {} ";"
	cp quad2-1_2_0.smt2.json ~/work/dReal/tools/ODE_visualization/data.json

k3:
	$(BMC) -k 3 quad3.drh
	time find . -name "quad3_3_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.1 --ode-grid=1024 --visualize $(OPT) {} ";"
	cp quad3_3_0.smt2.json ~/work/dReal/tools/ODE_visualization/data.json


k4:
	$(BMC) -k 4 quad4.drh
	time find . -name "quad4_4_*.smt2" -exec echo -n {} "    " ";" -exec $(DREAL) --precision=0.005 --ode-grid=1024 --visualize $(OPT) {} ";"
	cp quad4_4_0.smt2.json ~/work/dReal/tools/ODE_visualization/data.json

test:
	$(BMC) -k 0 test.drh
	$(DREAL) --precision=0.001 $(OPT) --visualize test_0_0.smt2
clean:
	rm -f *.preprocessed.drh
	rm -f *.smt2
	rm -f *.json
	rm -f *.proof
