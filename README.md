# Canonical Representation of Permutations Acting on Lists

(working with `Coq 8.13.0` and [`OLlibs 2.0.1`](https://github.com/olaure01/ollibs))

### Installation

Requires [OLlibs](https://github.com/olaure01/ollibs) (add-ons for the standard library): [see installation instructions](https://github.com/olaure01/ollibs/blob/master/README.md).

1. [install OLlibs](https://github.com/olaure01/ollibs/blob/master/README.md)
2. install development

        $ ./configure
        $ make
        $ make install

### Content

The files are listed in order of dependence: a file in the list may depend on the files above it.
The descriptions contain the notions that are introduced in the files.

- List_nat.v: Boolean properties and operators used to represent functions as lists of natural numbers.
- Fun_nat.v: Action of List nat over a list of arbitary elements. Identity function and cfun functions (circular shifts).
- Transposition.v: Consecutive and non-consecutive transpositions. Decomposition of a non-consecutive transpositions into a composition of consecutive ones.
- Perm.v: Properties of lists of natural numbers that represent permutations.
- Perm_R.v: Definition of Perm_R and basic properties.
- Perm_R_more.v: Less classical properties of Perm_R, necessary for the cut-elimination theorem of Linear Logic.
- CircularShift_R.v: Definition and properties of circular shift. Definition of a relation CircularShift_R, similar to Perm_R.v but using circular shifts instead of permutation.
- genperm_R.v: Factorized statements for different notions of permutation.
- mall.v: Multiplicative-additive fragment of Linear Logic, using Perm_R for the exchange rule. Cut-elimination theorem.
- mall_b.v: Factorization of MALL and cyMALL, using PCperm_R for the exchange rule. Cut-elimination theorem.
