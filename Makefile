
COQ = coqc -R $(OLLIBSDIR) ""
COQDOC = coqdoc -g

VFILES = $(wildcard *.v)

%.vo: %.v
	$(COQ) $<

%.glob: %.vo
	@true

%.html: %.v %.vo
	$(COQDOC) $<


doc: $(VFILES:.v=.glob)
	$(COQDOC) -toc $(VFILES)

clean:
	rm -f $(VFILES:.v=.vo)
	rm -f .*.aux
	rm -f *.crashcoqide
	rm -f *.glob
	rm -f *.html
	rm -f coqdoc.css
	rm -f lia.cache
	rm -f .lia.cache

.PHONY: clean
.PRECIOUS: %.vo %.glob


OLLIBSDIR = ../ollibs

.DEFAULT_GOAL := all

all: ollibs $(VFILES:.v=.vo)

ollibs:
	cd $(OLLIBSDIR) && $(MAKE)

include $(OLLIBSDIR)/ollibs.mk

length_lia.vo: length_lia.v $(OLLIBSDIR)/List_more.vo List_nat.vo Fun_nat.vo Transposition.vo

List_nat.vo: List_nat.v $(OLLIBSDIR)/Bool_more.vo $(OLLIBSDIR)/List_more.vo
Fun_nat.vo: Fun_nat.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/Bool_more.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo List_nat.vo
Transposition.vo: Transposition.v $(OLLIBSDIR)/Bool_more.vo $(OLLIBSDIR)/List_more.vo List_nat.vo Fun_nat.vo
Perm.vo: Perm.v $(OLLIBSDIR)/Bool_more.vo $(OLLIBSDIR)/List_Type_more.vo List_nat.vo length_lia.vo Fun_nat.vo Transposition.vo
Perm_R.vo : Perm_R.v $(OLLIBSDIR)/Permutation_Type.vo $(OLLIBSDIR)/Bool_more.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo List_nat.vo Fun_nat.vo Perm.vo length_lia.vo
Perm_R_more.vo : Perm_R_more.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo Fun_nat.vo Perm.vo Perm_R.vo
Perm_R_solve.vo : Perm_R_solve.v $(OLLIBSDIR)/List_more.vo Perm_R_more.vo
CircularShift_R.vo : CircularShift_R.v $(OLLIBSDIR)/Bool_more.vo $(OLLIBSDIR)/List_Type_more.vo List_nat.vo Perm.vo Perm_R_more.vo Fun_nat.vo length_lia.vo
CircularShift_R_solve.vo : CircularShift_R_solve.v $(OLLIBSDIR)/List_more.vo CircularShift_R.vo
genperm_R.vo : genperm_R.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_Type.vo Perm.vo Perm_R_more.vo Perm_R_solve.vo CircularShift_R.vo CircularShift_R_solve.vo length_lia.vo Fun_nat.vo
Perm_solve.vo : Perm_solve.v  $(OLLIBSDIR)/List_more.vo Perm.vo List_nat.vo Fun_nat.vo all_lt_solve.vo
all_lt_solve.vo : all_lt_solve.v List_nat.vo Fun_nat.vo Perm.vo length_lia.vo $(OLLIBSDIR)/List_more.vo

mall.vo : mall.v $(OLLIBSDIR)/Wf_nat_more.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo Perm_R_more.vo
mall_b.vo : mall_b.v $(OLLIBSDIR)/Wf_nat_more.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo genperm_R.vo
