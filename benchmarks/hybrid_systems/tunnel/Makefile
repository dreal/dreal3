BMC = ../../../tools/bmc/bmc.sh
DREAL = dReal
OPT =


k0:
	$(BMC) -i -p "[3]" -k 0 tunnel.drh
	$(DREAL) --precision=0.001 --ode-grid=256 $(OPT) --visualize tunnel_0.smt2

k2:
	$(BMC) -i -p "[3,2,1]" -k 2 tunnel.drh
	$(DREAL) --precision=0.001 --ode-grid=256 $(OPT) --visualize tunnel_2.smt2


k4:
	$(BMC) -i -p "[3,2,3,2,1]" -k 4 tunnel.drh
	$(DREAL) --precision=0.001 --ode-grid=256 $(OPT) --visualize tunnel_4.smt2

clean:
	rm -f *.preprocessed.drh
	rm -f *.smt2
	rm -f *.json
	rm -f *.proof
