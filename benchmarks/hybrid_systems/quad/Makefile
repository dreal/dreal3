DREACH = ../../../bin/dReach
OPT =

k0:
	$(DREACH) -k 0 quad0.drh --precision 0.01 --visualize $(OPT)

k1:
	$(DREACH) -k 1 quad1.drh --precision 0.01 --visualize $(OPT)

k2:
	$(DREACH) -l 2 -k 2 quad2.drh --precision 0.01 --visualize $(OPT)

k2-1:
	$(DREACH) -k 2 quad2-1.drh --precision 0.01 --visualize $(OPT)

k3:
	$(DREACH) -k 3 quad3.drh --precision 0.01  --visualize $(OPT)

k3-1:
	$(DREACH) -k 3 quad3-1.drh --precision 0.01 --visualize $(OPT)

k4:
	$(DREACH) -k 4 quad4.drh --precision 0.005 --ode_grid 1024 --visualize $(OPT)

clean:
	rm -f *.preprocessed.drh
	rm -f *.smt2
	rm -f *.json
	rm -f *.proof
	rm -f *.output
