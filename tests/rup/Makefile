INTERP = python3
PBIPDIR = ../../tools
CNFGEN = $(PBIPDIR)/pbip_cnf.py
PROOFGEN = $(PBIPDIR)/pbip_check.py
LRATDIR = ~/repos/drat-trim
LRAT = $(LRATDIR)/lrat-check
VLEVEL=1

.SUFFIXES: .ipbip .pbip .lrat .ldata

.ipbip.pbip:
	$(INTERP) $(CNFGEN) -v $(VLEVEL) -i $< -o $@ -c $*.cnf | tee $*.cnfdata

.pbip.lrat:
	$(INTERP) $(PROOFGEN) -v $(VLEVEL) -i $*.cnf -p $< -o $@ | tee $*.checkdata

.lrat.ldata:
	$(LRAT) $*.cnf $< | tee $@
