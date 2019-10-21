# Canonical Representation of Permutations Acting on Lists

The files List_more2.v and List_Type_more2.v contain additional properties on nth which are neither in the standard library nor in the ollibs library.

The files are listed in the order of dependence: a file in the list is dependent of the files above it.  
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