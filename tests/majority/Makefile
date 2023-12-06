INTERP = python3
GDIR=~/repos/pkc/benchmarks/generators
MGEN=$(GDIR)/gen_threshold.py
PBIPDIR = ../../tools
CNFGEN = $(PBIPDIR)/pbip_cnf.py
PROOFGEN = $(PBIPDIR)/pbip-check
PPROOFGEN = $(PBIPDIR)/pbip_check.py
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

.SUFFIXES: .ipbip .pbip .lrat .ldata .plrat .pldata .blrat .bldata

.ipbip.pbip:
	$(INTERP) $(CNFGEN) -v $(VLEVEL) -i $< -o $@ -c $*.cnf | tee $*.cnfdata

.pbip.lrat:
	$(PROOFGEN) -v $(VLEVEL) -i $*.cnf -p $< -o $@ | tee $*.checkdata

.lrat.ldata:
	$(LRAT) $*.cnf $< | tee $@

.pbip.blrat:
	$(PROOFGEN) -v $(VLEVEL) -S -i $*.cnf -p $< -o $@ | tee $*.checkdata

.blrat.bldata:
	$(LRAT) $*.cnf $< | tee $@


.pbip.plrat:
	$(INTERP) $(PPROOFGEN) -v $(VLEVEL) -i $*.cnf -p $< -o $@ | tee $*.checkdata

.plrat.pldata:
	$(LRAT) $*.cnf $< | tee $@

clean:
	rm -f *~
	rm -f *lrat
	rm -f *data

