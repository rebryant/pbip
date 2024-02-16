N=8
INTERP = python3
PBIPDIR = ../../tools
PGEN = ../generators/pigeon.py
CNFGEN = $(PBIPDIR)/pbip_cnf.py
PROOFGEN = $(PBIPDIR)/pbip_check.py
PROOFGEN = $(PBIPDIR)/pbip-check
LRATDIR = ~/repos/drat-trim
LRAT = $(LRATDIR)/lrat-check
VLEVEL=1

phpcp: php-cp-$(N).ipbip

phpcs: php-cs-$(N).ipbip

phpcc: php-cc-$(N).ipbip

phpep: php-ep-$(N).ipbip

phpes: php-es-$(N).ipbip

phpec: php-ec-$(N).ipbip


php-cp-$(N).ipbip: $(PGEN)
	$(INTERP) $(PGEN) -m p -n $(N) -v $(VLEVEL) -o $@ | tee $*.pdata

php-cs-$(N).ipbip: $(PGEN)
	$(INTERP) $(PGEN) -m s -n $(N) -v $(VLEVEL) -o $@ | tee $*.pdata

php-cc-$(N).ipbip: $(PGEN)
	$(INTERP) $(PGEN) -m c -n $(N) -v $(VLEVEL) -o $@ | tee $*.pdata

php-ep-$(N).ipbip: $(PGEN)
	$(INTERP) $(PGEN) -e -m p -n $(N) -v $(VLEVEL) -o $@ | tee $*.pdata

php-es-$(N).ipbip: $(PGEN)
	$(INTERP) $(PGEN) -e -m s -n $(N) -v $(VLEVEL) -o $@ | tee $*.pdata

php-ec-$(N).ipbip: $(PGEN)
	$(INTERP) $(PGEN) -e -m c -n $(N) -v $(VLEVEL) -o $@ | tee $*.pdata


.SUFFIXES: .ipbip .pbip .lrat .ldata

.ipbip.pbip:
	$(INTERP) $(CNFGEN) -v $(VLEVEL) -i $< -o $@ -c $*.cnf | tee $*.cnfdata

.pbip.lrat:
	$(PROOFGEN) -v $(VLEVEL) -i $*.cnf -p $< -o $@ | tee $*.checkdata

.lrat.ldata:
	$(LRAT) $*.cnf $< | tee $@
