INTERP = python3
GDIR=~/repos/pkc/benchmarks/generators
MGEN=$(GDIR)/gen_threshold.py
PBIPDIR = ../../tools
CNFGEN = $(PBIPDIR)/pbip_cnf.py
PROOFGEN = $(PBIPDIR)/pbip-check
LRATDIR = ~/repos/drat-trim
LRAT = $(LRATDIR)/lrat-check
CGEN = ./gen_cmaj.py

VLEVEL=2
N=5

majp: majp-$(N).pbip

majt: majt-$(N).pbip

cmaj: cmaj-$(N).ipbip

majp-$(N).pbip:
	$(INTERP) $(MGEN) -v 2 -P -n $(N) -r majp-$(N)

majt-$(N).pbip:
	$(INTERP) $(MGEN) -v 2 -P -n $(N) -t -r majt-$(N)

cmaj-$(N).ipbip:
	$(INTERP) $(CGEN) $(N) > cmaj-$(N).ipbip

.SUFFIXES: .ipbip .pbip .lrat .ldata

.ipbip.pbip:
	$(INTERP) $(CNFGEN) -v $(VLEVEL) -i $< -o $@ -c $*.cnf | tee $*.cnfdata

.pbip.lrat:
	$(PROOFGEN) -v $(VLEVEL) -i $*.cnf -p $< -o $@ | tee $*.checkdata

.lrat.ldata:
	$(LRAT) $*.cnf $< | tee $@
