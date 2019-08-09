ccmd = ghc -threaded --make
title = chorgram
debug = -auto-all -caf-all -rtsopts
ccdebug = $(ccmd) -Wall -threaded --make $(debug)
cfgfile = config.cfg
profiling = -prof -auto-all -caf-all
hkcpath := $(shell find . -type d -name 'hknt*')
petripath := $(shell find . -type d -name petrify)/bin
os := $(shell uname -s)
gitmsg = "checkpoint"

#
# Example of usage of scripts:
# python cfsm2gg.py -l -df png -dir <path-to-results-directory> <path-to-file>
# sgg.py --dot "Tpng" --dot "Gsplines=ortho" --sloppy -dir <path-to-results-directory> <path-to-file>
#


# compile: gmc.hs BuildGlobal.hs GGparser.hs SystemParser.hs sgg.hs sysparser.hs
#	$(ccmd)

compile: gmc.hs gg2graphml.hs BuildGlobal.hs GGparser.hs SystemParser.hs sgg.hs sysparser.hs minimise.hs gg2fsa.hs
	$(MAKE) all

all:
	$(ccmd) gmc.hs &&\
	$(ccmd) BuildGlobal.hs &&\
	$(ccmd) GGparser.hs &&\
	$(ccmd) SystemParser.hs &&\
	$(ccmd) sgg.hs &&\
	$(ccmd) sysparser.hs &&\
	$(ccmd) minimise.hs &&\
	$(ccmd) gg2fsa.hs
	$(ccmd) gg2graphml.hs

debug:
	$(ccdebug) gmc.hs &&\
	$(ccdebug) BuildGlobal.hs &&\
	$(ccdebug) GGparser.hs &&\
	$(ccdebug) SystemParser.hs &&\
	$(ccdebug) sgg.hs &&\
	$(ccdebug) sysparser.hs\
	$(ccdebug) gg2fsa.hs

# To get the stack trace, add +RTS -xc at the end of the gmc or BuildGlobal command
prof:
	$(ccmd) $(profiling) gmc.hs && ghc --make  $(profiling) BuildGlobal.hs

clean:
	@rm -f *~ *.o *.hi SystemParser.* GGparser.* gmc sgg BuildGlobal sysparser $(cfgfile) *.info *.log
	$(info >>> cleaning done.)

parser:
	happy -a -i  GGGrammar.y -o GGparser.hs && $(ccmd) GGparser.hs
	happy -a -i  RGGGrammar.y -o RGGparser.hs && $(ccmd) RGGparser.hs
	happy -a -i  SystemGrammar.y -o SystemParser.hs && $(ccmd) SystemParser.hs

config:
	@echo "hkc\t"$(hkcpath) > /tmp/$(cfgfile)
	@echo "petry\t"$(petripath) >> /tmp/$(cfgfile)
	@echo "gmc\t./gmc" >> /tmp/$(cfgfile)
	@echo "bg\t./BuildGlobal" >> /tmp/$(cfgfile)
	@mv /tmp/$(cfgfile) $(cfgfile)
	$(info >>> config file for the python script created.)

hp:
	@if test -e $(hkcpath)/hkc; then echo ">>> The binary of hkc is already there. Nothing to be done."; else make -C $(hkcpath); echo ">>> hkc compiled"; fi
	@if test -e $(hkcpath)/hkc$(os); then echo ">>> The link to hkc is already there. Nothing to be done."; else (cd $(hkcpath); ln -s hkc hkc$(os)) ; echo ">>> link to petrify added"; fi
	@if test -e $(petripath)/petrify$(os); then echo ">>> The link to petrify is already there. Nothing to be done."; else (cd $(petripath); ln -s petrify petrify$(os)); fi

setup:
	make config
	make hp
	make parser
	make all

e:
	e -T $(title) gmc.hs &

git:
	git pull
	git commit -am $(gitmsg) && git push