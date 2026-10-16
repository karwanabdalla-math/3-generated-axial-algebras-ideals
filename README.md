# Ideals in 3-generated primitive axial algebras of Jordan type ½ — computer calculations

This repository contains the GAP code verifying the computations in the paper

> *[Title of the paper]*, [Author(s)], [arXiv / journal reference].

All checks are **symbolic**: the parameters ζ, β, γ, ψ (with α = (ζ+1)²/(4ζ))
and the auxiliary variables are indeterminates over ℚ, so each verified
identity holds for all parameter values (with ζ ≠ 0, ±1), over every field of
characteristic different from 2.

## Requirements

[GAP](https://www.gap-system.org) 4.12 or later (tested with GAP 4.15.1).
No additional packages are needed.

## How to run

Start GAP in the folder containing the files and type, for example,

```
Read("check_Lemma_3_15.g");
```

Each file prints one line per check, followed by

```
ALL CHECKS PASSED: true
```

Running times range from a few seconds (`check_Remark_3_21.g`) to a few
minutes (`check_main.g`).

## Files

| File | Results verified in the paper |
|---|---|
| `check_permutation_symmetry.g` | Remark 2.21: the universal algebra is symmetric under all permutations of the generators *a, b, c* |
| `check_Lemma_3_15.g` | Lemma 3.15 (the operator C_W), and all computations of Section 3.1: Proposition 2.23, Lemma 3.2, Proposition 3.3, Lemma 3.13, Remark 3.14 |
| `check_Props_3_18-3_22.g` | Propositions 3.18–3.22: the ideals M_[x:y], D₁⊕M_[x:y], D₀⊕M_[x:y], D₀⊕D₁⊕M_[x:y] |
| `check_Remark_3_21.g` | Remark 3.21 (the discriminant of the quadratic form Q) and Example 4.5 |
| `check_Prop_3_23_Lemma_3_24.g` | Proposition 3.23 and Lemma 3.24 (the B-component C_B on W) |
| `check_Section_4.g` | Lemma 4.1, Lemma 4.2 and Example 4.4 |
| `check_main.g` | **All of the above in one file**, together with the remaining computations of Sections 3–4 (the cases L = 0 and L = X, Lemma 3.25, Proposition 3.32) |

The files other than `check_permutation_symmetry.g` and
`check_Remark_3_21.g` first rebuild the setup of Section 3.1 and check it
silently; the detailed checks of that setup are in `check_Lemma_3_15.g`.

## Conventions

* The multiplication table of the universal algebra A(α, β, γ, ψ) is
  transcribed from Gorshkov–Staroletov, *J. Algebra* 563 (2020), Table 1,
  and the Frobenius form from Table 5 of the same paper. As a check of the
  transcription, the code verifies the Jordan identity, the eigenvalues of
  ad_a, and the associativity of the form on all 729 triples of basis
  elements.
* Basis order of A (as in Gorshkov–Staroletov):
  a, b, c, ab, bc, ac, a(bc), b(ac), c(ab).
* The basis (e₁, …, e₆) of W = B^⊥ is e₁ = c°, e₂ = (bc)°, e₃ = (ac)°,
  e₄ = a(bc)°, e₅ = b(ac)°, e₆ = c(ab)°, where x° is the projection of x
  onto W.
* Normalization of the toric basis {s, 1_B, t} of B = ⟨⟨a, b⟩⟩:
  a = d₁ and b = d_{1/ζ}, where d_ξ = ξ s + ½ 1_B + ξ⁻¹ t.
