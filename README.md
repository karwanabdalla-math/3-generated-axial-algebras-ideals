Ideals of 3-generated primitive axial algebras of Jordan type 1/2
GAP code verifying the computations in the paper
> Karwan Abdalla, **The lattice of ideals of 3-generated primitive axial algebras of Jordan type 1/2**.
The paper studies the 9-dimensional universal algebra A(α, β, γ, ψ) of Gorshkov and Staroletov
(J. Algebra 563 (2020), 74–99), with basis
    a, b, c, ab, bc, ac, p = a(bc), q = b(ac), r = c(ab)

in this order. The multiplication table is taken from [GS, Table 1] and the Gram matrix of the
Frobenius form from [GS, Table 5]; the associativity of the form is verified in `check_main.g`,
which also checks the transcription of both tables (used for Table 1 of the paper). All files
use the same transcription of the tables, copied character for character.
Requirements
GAP 4.15.1 (the files use only the standard library;
the MeatAxe, used in several files, is part of it).
How to run
Download a file and read it into GAP, for example
```gap
Read(Filename(DirectoryHome(), "Downloads/check_main.g"));
```
Every file is self-contained, prints one line per check, and ends with
```
ALL CHECKS PASSED: true
```
Sections 2–4: algebras with a toric line
Parameters are treated as indeterminates wherever possible, so the checks hold identically,
for all parameter values, over every field of characteristic not 2.
File	Verifies
`check_permutation_symmetry.g`	Remark 2.21 (symmetry under permutations of a, b, c)
`check_main.g`	the transcription of [GS, Tables 1 and 5] (Table 1), and all computations of Sections 3 and 4 in one file; Part 16: Proposition 4.6 (descent when ζ ∉ 𝔽)
`check_Lemma_3_15.g`	Section 3.1 and Lemma 3.15 (the operator C_W)
`check_Props_3_18-3_22.g`	Propositions 3.18–3.22, at every point [x:y] of the projective line
`check_Remark_3_21.g`	Remark 3.21 and Example 4.5
`check_Prop_3_23_Lemma_3_24.g`	Proposition 3.23 and Lemma 3.24
`check_Section_4.g`	Lemmas 4.1 and 4.2 and Example 4.4
`check_Props_3_18-3_22.g` first checks the equivalences at a generic point [x:1] (Part A) and
the vanishing of C_B (Part B), and then shows that they hold at every point (Part C): the
C_W-condition has constant rank in x, the stated conditions imply it with poles only at
x = 0, −1, ζ − 1 and (x + 1)² = ζ, and these special points, together with [1:0], are checked
directly. It runs in about 4–5 minutes.
Section 5: algebras with a hidden toric line
File	Verifies
`check_hidden_toric.g`	Lemma 5.1, Table 3, Corollary 5.2 and Remark 5.3(a); also dim A^⊥ for the first four rows of Proposition 6.6
`check_hidden_toric.g` consists of five parts:
symbolic: τ_a and τ_c are automorphisms preserving the form, and the new form values of Lemma 5.1;
the four algebras of Table 3: dim A^⊥ in every odd characteristic, new parameters, and a direct
check that A is isomorphic to the universal algebra for the new triple (all 81 products);
cross-check of Corollary 5.2 by listing all ideals over GF(5), GF(7), GF(11), GF(13) with the MeatAxe;
characteristic 3: the Miyamoto closure of {a, b, c} has 18 axes and contains no toric pair (Remark 5.3(a));
Corollary 5.2(a): A w = 0, the ideals I_1 and I_2 are defined over Z[1/2], dim(I_1 + I_2) = 5 in
every odd characteristic, and the transposition (a b) maps I_1 onto I_2.
It runs in about 3–4 minutes.
Section 6: algebras without a toric line
Each file below also checks, where relevant, that the bases used are bases in every
characteristic not 2 (all coefficients lie in Z[1/2], and the relevant elementary divisors or
determinants are powers of 2), and cross-checks the classification against a complete list of
ideals over small finite fields, computed with the MeatAxe.
File	Section	Verifies
`check_Section_6_1.g`	6.1	Lemma 6.3: y(xy) = ((x,y) y + xy)/2 for x ≠ y in {a, b, c}, symbolically
`check_Section_6_2.g`	6.2	Proposition 6.6: dim A^⊥ for (0,0,0,0), (0,0,1,0), (1,1,1,1), (0,1,1,0), (1,1,1,−1) in every odd characteristic; Proposition 6.8: the elements of A^⊥ and the spanning by the axes that give A/A^⊥ ≅ 𝔽^k
`check_Section_6_3.g`	6.3	the algebra (0,0,0,0): A^⊥, the action of a, b, c, the families N^{ab} (symbolically in λ, μ), the block I_a; Remark 6.13: number of ideals over GF(5), GF(7)
`check_Section_6_4.g`	6.4	the algebra (0,0,1,0): basis of A^⊥, the action table, the ideals N_ℓ (symbolically in λ, μ), the block I_b; number of ideals over GF(3), GF(5), GF(7)
`check_Section_6_5.g`	6.5	the algebra (1,1,1,1): Lemma 6.18 (basis of A^⊥, the action formulas, symbolically in d), Δ(d), the ideals M_m (symbolically in m) and Q_d; number of ideals over GF(3), GF(5), GF(7), GF(11)
`check_Section_6_6.g`	6.6	Theorem 6.22: bases of A^⊥, the action of a, b, c, and the determinants showing that L_a, L_b, L_c generate End(A^⊥); Proposition 6.23: the toric line in characteristic 3; Proposition 6.24: cross-check of the simple case over GF(p), p ≤ 19
The files `check_Section_6_3.g`, `check_Section_6_4.g` and `check_Section_6_5.g` take one to
three minutes each; the others take a few seconds.
Reference
[GS] I. Gorshkov, A. Staroletov, On primitive 3-generated axial algebras of Jordan type,
J. Algebra 563 (2020), 74–99. https://doi.org/10.1016/j.jalgebra.2020.07.014
