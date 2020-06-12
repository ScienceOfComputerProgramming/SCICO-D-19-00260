SOURCE=../experiments/ice2020/atm_fixed.sgg
EXPERIMENT_NAME=atm_fixed

all:
	python3 ../../rgg2erl.py -rg ${EXPERIMENT_NAME} -df png --sloppy --dir ${EXPERIMENT_NAME} ${SOURCE}

setup:
	erlc aux.erl
	erlc rgg_support.erl
	erlc gg2erl.erl
	erlc ${EXPERIMENT_NAME}/${EXPERIMENT_NAME}.erl

run: 
	erl -eval '$(EXPERIMENT_NAME):main()' -s init stop
	erlc $(EXPERIMENT_NAME)_$(EXPERIMENT_NAME).erl
	erl -eval '$(EXPERIMENT_NAME)_$(EXPERIMENT_NAME):main()' -s init stop
