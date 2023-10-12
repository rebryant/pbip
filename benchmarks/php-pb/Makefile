N=8
INTERP = python3
PBIPDIR = ../../tools
PGEN = ../generators/pigeon.py
CNFGEN = $(PBIPDIR)/pbip_cnf.py
PROOFGEN = $(PBIPDIR)/pbip_check.py
LRATDIR = ~/repos/drat-trim
LRAT = $(LRATDIR)/lrat-check
VLEVEL=1

php: php-$(N).ipbip

phpe: phpe-$(N).ipbip

php-all: php-$(N).ipbip php-$(N).pbip php-$(N).lrat php-$(N).ldata
	cat php-$(N).{pdata,cnfdata,checkdata} > php-$(N).data

phpe-all: phpe-$(N).ipbip phpe-$(N).pbip phpe-$(N).lrat phpe-$(N).ldata
	cat phpe-$(N).{pdata,cnfdata,checkdata} > phpe-$(N).data

php-$(N).ipbip: $(PGEN)
	$(INTERP) $(PGEN) -n $(N) -v $(VLEVEL) -o $@ | tee $*.pdata

phpe-$(N).ipbip: $(PGEN)
	$(INTERP) $(PGEN) -e -n $(N) -v $(VLEVEL) -o $@ | tee $*.pdata

.SUFFIXES: .ipbip .pbip .lrat .ldata

.ipbip.pbip:
	$(INTERP) $(CNFGEN) -v $(VLEVEL) -i $< -o $@ -c $*.cnf | tee $*.cnfdata

.pbip.lrat:
	$(INTERP) $(PROOFGEN) -v $(VLEVEL) -i $*.cnf -p $< -o $@ | tee $*.checkdata

.lrat.ldata:
	$(LRAT) $*.cnf $< | tee $@
