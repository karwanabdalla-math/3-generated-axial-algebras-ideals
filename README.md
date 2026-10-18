# Ideals of 3-generated primitive axial algebras of Jordan type 1/2

GAP code verifying the computations in the paper

> Karwan Abdalla, **The lattice of ideals of 3-generated primitive axial algebras of Jordan type 1/2**.

The paper studies the 9-dimensional universal algebra A(α, β, γ, ψ) of Gorshkov and Staroletov
(J. Algebra 563 (2020), 74–99), with basis

    a, b, c, ab, bc, ac, p = a(bc), q = b(ac), r = c(ab)

in this order. The multiplication table is taken from [GS, Table 1] and the Gram matrix of the
Frobenius form from [GS, Table 5]; the associativity of the form is verified in `check_main.g`,
which also checks the transcription of both tables.

## Requirements

- [GAP](https://www.gap-system.org) 4.15.1 (the files use only the standard library;
  the MeatAxe, used in `check_hidden_toric.g`, is part of it).

## How to run

Download a file and read it into GAP, for example

```gap
Read(Filename(DirectoryHome(), "Downloads/check_main.g"));
```

Every file is self-contained, prints one line per check, and ends with

```
ALL CHECKS PASSED: true
```

## Files

Parameters are treated as indeterminates wherever possible, so the checks hold identically,
for all parameter values, over every field of characteristic not 2.

| File | Verifies |
|---|---|
| `check_permutation_symmetry.g` | Remark 2.21 (symmetry under permutations of a, b, c) |
| `check_Lemma_3_15.g` | Section 3.1 and Lemma 3.15 (the operator C_W) |
| `check_Props_3_18-3_22.g` | Propositions 3.18–3.22 |
| `check_Remark_3_21.g` | Remark 3.21 and Example 4.5 |
| `check_Prop_3_23_Lemma_3_24.g` | Proposition 3.23 and Lemma 3.24 |
| `check_Section_4.g` | Lemmas 4.1 and 4.2 and Example 4.4 |
| `check_hidden_toric.g` | Section 4.4: Lemma 4.7, Table 1, Corollary 4.8 and Remark 4.9 |
| `check_main.g` | all computations of Sections 3 and 4.1–4.3 in one file |

`check_hidden_toric.g` consists of five parts:

1. symbolic: τ_a and τ_c are automorphisms preserving the form, and the new form values of Lemma 4.7;
2. the four algebras of Table 1: new parameters, and a direct check that A is isomorphic to the
   universal algebra for the new triple (all 81 products);
3. cross-check of Corollary 4.8 by listing all ideals over GF(5), GF(7), GF(11), GF(13) with the MeatAxe;
4. characteristic 3: the Miyamoto closure of {a, b, c} has 18 axes and contains no toric pair (Remark 4.9);
5. the two 3-dimensional ideals of Corollary 4.8(a) are defined over Z[1/2], hence over every
   field of characteristic not 2.

It runs in about 3–4 minutes.

## Reference

[GS] I. Gorshkov, A. Staroletov, On primitive 3-generated axial algebras of Jordan type,
J. Algebra 563 (2020), 74–99. https://doi.org/10.1016/j.jalgebra.2020.07.014
