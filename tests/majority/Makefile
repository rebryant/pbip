INTERP = python3
PBIPDIR = ../../tools
PROOFGEN = $(PBIPDIR)/pbip-check
PPROOFGEN = $(PBIPDIR)/pbip_check.py
LRATDIR = ~/repos/drat-trim
LRAT = $(LRATDIR)/lrat-check
CGEN = ./gen_cmaj.py

VLEVEL=2
N=5

cmaj-sc: cmaj-sc-$(N).pbip

cmaj-sn: cmaj-sn-$(N).pbip

cmaj-cn: cmaj-cn-$(N).pbip

cmaj-tz: cmaj-tz-$(N).pbip

cmaj-mt: cmaj-mt-$(N).pbip

cmaj-kt: cmaj-kt-$(N).pbip

cmaj-sc-$(N).pbip:
	$(INTERP) $(CGEN) -n $(N) -e seqcounter -p $@ -c $*.cnf 

cmaj-sn-$(N).pbip:
	$(INTERP) $(CGEN) -n $(N) -e sortnetwrk -p $@ -c $*.cnf 

cmaj-cn-$(N).pbip:
	$(INTERP) $(CGEN) -n $(N) -e cardnetwrk -p $@ -c $*.cnf 

cmaj-tz-$(N).pbip:
	$(INTERP) $(CGEN) -n $(N) -e totalizer -p $@ -c $*.cnf 

cmaj-mt-$(N).pbip:
	$(INTERP) $(CGEN) -n $(N) -e mtotalizer -p $@ -c $*.cnf 

cmaj-kt-$(N).pbip:
	$(INTERP) $(CGEN) -n $(N) -e kmtotalizer -p $@ -c $*.cnf 


.SUFFIXES: .pbip .lrat .ldata .plrat .pldata .blrat .bldata

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

