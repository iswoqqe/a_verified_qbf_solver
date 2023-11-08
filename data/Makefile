default: domino_instances.zip xor_instances.zip

domino_numbers := 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15
domino_instances := $(patsubst %,domino%.qdimacs,${domino_numbers})
domino_inverse_instances := $(patsubst %,domino%i.qdimacs,${domino_numbers})

domino_instances.zip: ${domino_instances} ${domino_inverse_instances}
	zip domino_instances.zip $^

${domino_instances}: domino%.qdimacs:
	python -B domino_game.py -n $* > domino$*.qdimacs

${domino_inverse_instances}: domino%i.qdimacs:
	python -B domino_game.py -i -n $* > domino$*i.qdimacs

xor_numbers := 1 2 3 4 5 6 7 8 9 10 15 20 25 30 60 100 300 600 1000 3000 6000 10000
xor_sat_instances := $(patsubst %,xor%_sat.qdimacs,${xor_numbers})
xor_unsat_instances := $(patsubst %,xor%_unsat.qdimacs,${xor_numbers})

xor_instances.zip: ${xor_sat_instances} ${xor_unsat_instances}
	zip xor_instances.zip $^

${xor_sat_instances}: xor%_sat.qdimacs:
	bash gen_xor.sh $* > $@

${xor_unsat_instances}: xor%_unsat.qdimacs:
	bash gen_xor.sh $* t > $@

clean_most:
	${RM} ${domino_instances} ${domino_inverse_instances} ${xor_sat_instances} ${xor_unsat_instances}

clean: clean_most
	${RM} domino_instances.zip xor_instances.zip

.PHONY: default clean clean_most
