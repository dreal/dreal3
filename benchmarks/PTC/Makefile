DREAL = ../../bin/dReal
OPT =

barrier:
	$(DREAL) --precision=0.00001 $(OPT) $@.smt2

init_inside_levelset:
	$(DREAL) --precision=0.000001 $(OPT) $@.smt2

levelset_size:
	$(DREAL) --precision=0.0001 $(OPT) $@.smt2

clean:
	rm -f *.json
	rm -f *.proof
