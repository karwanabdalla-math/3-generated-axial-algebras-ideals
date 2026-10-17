#############################################################################
##  check_hidden_toric.g
##
##  Verification of Section 4.5 (algebras with a hidden toric line).
##  Basis order as in [GS, Table 1] and check_main.g:
##    1:a  2:b  3:c  4:ab  5:bc  6:ac  7:p=a(bc)  8:q=b(ac)  9:r=c(ab)
##
##  Part 1: symbolic (alpha, beta, gamma, psi indeterminates):
##          tau_x is an automorphism preserving the form; new form values.
##  Part 2: the four algebras; new generating triples; explicit
##          isomorphism with the universal algebra for the new parameters.
##  Part 3: ideal lattices over GF(p) by the MeatAxe (cross-check).
##  Part 4: characteristic 3: the Miyamoto closure of {a,b,c} has no
##          toric pair, so the reduction does not apply there.
#############################################################################

## Multiplication table of A(al,be,ga,ps) from [GS, Table 1]
## (identical to check_main.g).
CURZERO := 0;;
Vec := function(pairs)
  local v, pr;
  v := List([1..9], i -> CURZERO);
  for pr in pairs do v[pr[1]] := v[pr[1]] + pr[2]; od;
  return v;
end;;
MakeTable := function(al, be, ga, ps)
  local T, S, a, b, c, ab, bc, ac, p, q, r;
  a:=1; b:=2; c:=3; ab:=4; bc:=5; ac:=6; p:=7; q:=8; r:=9;
  CURZERO := Zero(al);
  T := List([1..9], i -> List([1..9], j -> fail));
  S := function(i, j, v) T[i][j] := v; T[j][i] := v; end;
  S(a,a, Vec([[a,1]]));  S(b,b, Vec([[b,1]]));  S(c,c, Vec([[c,1]]));
  S(a,b, Vec([[ab,1]])); S(a,c, Vec([[ac,1]])); S(b,c, Vec([[bc,1]]));
  S(a,bc, Vec([[p,1]])); S(b,ac, Vec([[q,1]])); S(c,ab, Vec([[r,1]]));
  S(a,ab, Vec([[a,al/2],[ab,1/2]]));  S(a,ac, Vec([[a,ga/2],[ac,1/2]]));
  S(b,ab, Vec([[b,al/2],[ab,1/2]]));  S(b,bc, Vec([[b,be/2],[bc,1/2]]));
  S(c,ac, Vec([[c,ga/2],[ac,1/2]]));  S(c,bc, Vec([[c,be/2],[bc,1/2]]));
  S(a,p, Vec([[a,ps/2],[p,1/2]]));
  S(b,q, Vec([[b,ps/2],[q,1/2]]));
  S(c,r, Vec([[c,ps/2],[r,1/2]]));
  S(a,q, (1/4)*Vec([[a,ps],[ab,ga],[ac,al],[p,1],[q,1],[r,-1]]));
  S(a,r, (1/4)*Vec([[a,ps],[ab,ga],[ac,al],[p,1],[q,-1],[r,1]]));
  S(b,p, (1/4)*Vec([[b,ps],[ab,be],[bc,al],[p,1],[q,1],[r,-1]]));
  S(b,r, (1/4)*Vec([[b,ps],[ab,be],[bc,al],[p,-1],[q,1],[r,1]]));
  S(c,p, (1/4)*Vec([[c,ps],[bc,ga],[ac,be],[p,1],[q,-1],[r,1]]));
  S(c,q, (1/4)*Vec([[c,ps],[bc,ga],[ac,be],[p,-1],[q,1],[r,1]]));
  S(ab,ab, Vec([[a,al/4],[b,al/4],[ab,al/2]]));
  S(bc,bc, Vec([[b,be/4],[c,be/4],[bc,be/2]]));
  S(ac,ac, Vec([[a,ga/4],[c,ga/4],[ac,ga/2]]));
  S(ab,bc, (1/4)*Vec([[b,ps],[ab,be],[bc,al],[p,1],[q,-1],[r,1]]));
  S(bc,ac, (1/4)*Vec([[c,ps],[bc,ga],[ac,be],[p,1],[q,1],[r,-1]]));
  S(ab,ac, (1/4)*Vec([[a,ps],[ab,ga],[ac,al],[p,-1],[q,1],[r,1]]));
  S(ab,p, (1/8)*Vec([[a,al*be+ps],[b,ps],[ab,2*ps],[bc,al],[p,2*al]]));
  S(ab,q, (1/8)*Vec([[a,ps],[b,al*ga+ps],[ab,2*ps],[ac,al],[q,2*al]]));
  S(bc,q, (1/8)*Vec([[b,be*ga+ps],[c,ps],[bc,2*ps],[ac,be],[q,2*be]]));
  S(bc,r, (1/8)*Vec([[b,ps],[c,al*be+ps],[ab,be],[bc,2*ps],[r,2*be]]));
  S(ac,p, (1/8)*Vec([[a,be*ga+ps],[c,ps],[bc,ga],[ac,2*ps],[p,2*ga]]));
  S(ac,r, (1/8)*Vec([[a,ps],[c,al*ga+ps],[ab,ga],[ac,2*ps],[r,2*ga]]));
  S(ab,r, (1/8)*Vec([[a,al*be],[b,al*ga],[ab,4*ps],[bc,al],[ac,al],
                     [p,-2*al],[q,-2*al],[r,4*al]]));
  S(bc,p, (1/8)*Vec([[b,be*ga],[c,al*be],[ab,be],[bc,4*ps],[ac,be],
                     [p,4*be],[q,-2*be],[r,-2*be]]));
  S(ac,q, (1/8)*Vec([[a,be*ga],[c,al*ga],[ab,ga],[bc,ga],[ac,4*ps],
                     [p,-2*ga],[q,4*ga],[r,-2*ga]]));
  S(p,p, (1/16)*Vec([[a,be*(al+ga+2*ps)],[b,be*ga],[c,al*be],[bc,4*ps],
                     [p,2*be+8*ps],[q,-2*be],[r,-2*be]]));
  S(q,q, (1/16)*Vec([[a,be*ga],[b,ga*(al+be+2*ps)],[c,al*ga],[ac,4*ps],
                     [p,-2*ga],[q,2*ga+8*ps],[r,-2*ga]]));
  S(r,r, (1/16)*Vec([[a,al*be],[b,al*ga],[c,al*(be+ga+2*ps)],[ab,4*ps],
                     [p,-2*al],[q,-2*al],[r,2*al+8*ps]]));
  S(p,q, (1/16)*Vec([[a,be*(ga+ps)],[b,ga*(be+ps)],[c,al*ps],[ab,2*ps],
                     [bc,2*(al*ga+ps)],[ac,2*(al*be+ps)],
                     [p,4*ps-al+be-ga],[q,4*ps-al-be+ga],[r,al-be-ga-4*ps]]));
  S(q,r, (1/16)*Vec([[a,be*ps],[b,ga*(al+ps)],[c,al*(ga+ps)],
                     [ab,2*(be*ga+ps)],[bc,2*ps],[ac,2*(al*be+ps)],
                     [p,be-al-ga-4*ps],[q,4*ps-al-be+ga],[r,4*ps+al-be-ga]]));
  S(r,p, (1/16)*Vec([[a,be*(al+ps)],[b,ga*ps],[c,al*(be+ps)],
                     [ab,2*(be*ga+ps)],[bc,2*(al*ga+ps)],[ac,2*ps],
                     [p,4*ps-al+be-ga],[q,ga-al-be-4*ps],[r,4*ps+al-be-ga]]));
  return T;
end;;

MakeGram := function(al, be, ga, ps)
  local G, SetG;
  G := NullMat(9, 9, Zero(al));
  SetG := function(i, j, v) G[i][j] := v; G[j][i] := v; end;
  SetG(1,1,1); SetG(1,2,al); SetG(1,3,ga); SetG(1,4,al); SetG(1,5,ps); SetG(1,6,ga);
  SetG(1,7,ps); SetG(1,8,(al*ga+ps)/2); SetG(1,9,(al*ga+ps)/2);
  SetG(2,2,1); SetG(2,3,be); SetG(2,4,al); SetG(2,5,be); SetG(2,6,ps);
  SetG(2,7,(al*be+ps)/2); SetG(2,8,ps); SetG(2,9,(al*be+ps)/2);
  SetG(3,3,1); SetG(3,4,ps); SetG(3,5,be); SetG(3,6,ga);
  SetG(3,7,(be*ga+ps)/2); SetG(3,8,(be*ga+ps)/2); SetG(3,9,ps);
  SetG(4,4,al^2/2+al/2); SetG(4,5,al*be/2+ps/2); SetG(4,6,al*ga/2+ps/2);
  SetG(4,7,(al*be+ps+2*al*ps)/4); SetG(4,8,(al*ga+ps+2*al*ps)/4);
  SetG(4,9,al*(be+ga+2*ps)/4);
  SetG(5,5,be^2/2+be/2); SetG(5,6,be*ga/2+ps/2);
  SetG(5,7,be*(al+ga+2*ps)/4); SetG(5,8,(be*ga+ps+2*be*ps)/4);
  SetG(5,9,(al*be+ps+2*be*ps)/4);
  SetG(6,6,ga^2/2+ga/2); SetG(6,7,(be*ga+ps+2*ga*ps)/4);
  SetG(6,8,ga*(al+be+2*ps)/4); SetG(6,9,(al*ga+ps+2*ga*ps)/4);
  SetG(7,7,(al*be+be*ga+2*ps*be+4*ps^2)/8);
  SetG(7,8,(2*al*be*ga+al*ps+ga*ps+be*ga+be*ps+2*ps^2)/8);
  SetG(7,9,(2*al*be*ga+al*be+ga*ps+al*ps+be*ps+2*ps^2)/8);
  SetG(8,8,(al*ga+be*ga+2*ga*ps+4*ps^2)/8);
  SetG(8,9,(2*al*be*ga+al*ga+ga*ps+al*ps+be*ps+2*ps^2)/8);
  SetG(9,9,(al*be+al*ga+2*al*ps+4*ps^2)/8);
  return G;
end;;

Mult := function(T, x, y)
  local z, i, j;
  z := List([1..9], i -> Zero(x[1]));
  for i in [1..9] do
    if not IsZero(x[i]) then
      for j in [1..9] do
        if not IsZero(y[j]) then z := z + x[i]*y[j]*T[i][j]; fi;
      od;
    fi;
  od;
  return z;
end;;

Same := function(x, y)
  if IsList(x) then
    return Length(x) = Length(y) and ForAll([1..Length(x)], i -> Same(x[i], y[i]));
  fi;
  return IsZero(x - y);
end;;

results := [];;
Report := function(name, ok)
  Add(results, ok);
  Print(String(name, -66), " ", ok, "\n");
end;;

## The Miyamoto involution tau_x(y) = y - 4 xy + 4 (x,y) x.
MiyTau := function(T, G, x, y)
  return y - 4*Mult(T, x, y) + 4*(x*G*y)*x;
end;;

#############################################################################
Print("\n--- 1. Symbolic part: tau_a, tau_c and the new form values ---\n");
#############################################################################
al := Indeterminate(Rationals, "alpha");;
be := Indeterminate(Rationals, "beta");;
ga := Indeterminate(Rationals, "gamma");;
ps := Indeterminate(Rationals, "psi");;
T := MakeTable(al, be, ga, ps);;
G := MakeGram(al, be, ga, ps);;
Ebas := IdentityMat(9, al);;
a := Ebas[1];; b := Ebas[2];; c := Ebas[3];;
M := function(x, y) return Mult(T, x, y); end;;
F := function(x, y) return x*G*y; end;;

tau := 0;; TauV := 0;;
for ax in [[a, "a"], [c, "c"]] do
  tau := List([1..9], i -> MiyTau(T, G, ax[1], Ebas[i]));    # images of basis vectors
  TauV := v -> v * tau;
  Report(Concatenation("tau_", ax[2], " is an automorphism of A (81 products)"),
    ForAll(Cartesian([1..9],[1..9]), ij ->
      Same(M(tau[ij[1]], tau[ij[2]]), TauV(T[ij[1]][ij[2]]))));
  Report(Concatenation("tau_", ax[2], "^2 = id"),
    ForAll([1..9], i -> Same(TauV(tau[i]), Ebas[i])));
  Report(Concatenation("tau_", ax[2], " preserves the Frobenius form"),
    ForAll(Cartesian([1..9],[1..9]), ij ->
      Same(F(tau[ij[1]], tau[ij[2]]), G[ij[1]][ij[2]])));
od;

cp := MiyTau(T, G, a, c);;     # c' = tau_a(c)
bp := MiyTau(T, G, c, b);;     # b' = tau_c(b)
Report("c' := tau_a(c) = c - 4ac + 4 gamma a",
  Same(cp, c - 4*M(a,c) + 4*ga*a));
Report("(c',c') = 1, (a,c') = gamma",
  Same(F(cp,cp), 1) and Same(F(a,cp), ga));
Report("(b,c') = beta - 4 psi + 4 alpha gamma",
  Same(F(b,cp), be - 4*ps + 4*al*ga));
Report("(a, b c') = (b, a c') = (c', ab) = -psi + 2 alpha gamma",
  Same(F(a, M(b,cp)), -ps + 2*al*ga) and Same(F(b, M(a,cp)), -ps + 2*al*ga)
  and Same(F(cp, M(a,b)), -ps + 2*al*ga));
Report("b' := tau_c(b):  (b',b') = 1, (b',c) = beta",
  Same(F(bp,bp), 1) and Same(F(bp,c), be));
Report("(a,b') = alpha - 4 psi + 4 beta gamma",
  Same(F(a,bp), al - 4*ps + 4*be*ga));
Report("(a, b' c) = (b', ac) = (c, a b') = -psi + 2 beta gamma",
  Same(F(a, M(bp,c)), -ps + 2*be*ga) and Same(F(bp, M(a,c)), -ps + 2*be*ga)
  and Same(F(c, M(a,bp)), -ps + 2*be*ga));

#############################################################################
Print("\n--- 2. The four algebras with a hidden toric line ---\n");
#############################################################################
## For a triple (x1,x2,x3) in A, the parameters of the triple, in the
## convention alpha=(x1,x2), beta=(x2,x3), gamma=(x1,x3), psi=(x1,x2x3).
TripleParams := function(T, G, x)
  return [x[1]*G*x[2], x[2]*G*x[3], x[1]*G*x[3], x[1]*G*Mult(T, x[2], x[3])];
end;;
## Images in A of the standard basis of the universal algebra of the triple.
TripleBasis := function(T, x)
  local m;
  m := function(u, v) return Mult(T, u, v); end;
  return [x[1], x[2], x[3], m(x[1],x[2]), m(x[2],x[3]), m(x[1],x[3]),
          m(x[1], m(x[2],x[3])), m(x[2], m(x[1],x[3])), m(x[3], m(x[1],x[2]))];
end;;
## phi: A(new params) -> A, e_i -> N[i], is an algebra isomorphism.
IsIso := function(T, N, Tnew)
  return RankMat(N) = 9 and ForAll(Cartesian([1..9],[1..9]), ij ->
    Same(Mult(T, N[ij[1]], N[ij[2]]), Tnew[ij[1]][ij[2]] * N));
end;;
ThetaOf := p -> p[1] + p[2] + p[3] - 2*p[4] - 1;;
SigmaOf := p -> p[1]*p[2]*p[3] - p[4]^2;;

## Each case: original (alpha,beta,gamma,psi), name of new triple,
## the new triple as a function of (T,G), expected new parameters,
## expected dim A^perp, expected Paper 1 case.
E9 := IdentityMat(9, Rationals);; T0 := 0;; G0 := 0;; T3 := 0;; G3 := 0;; one := 0;; AX := 0;;
Cases := [
  rec(par := [0,0,0,-1/2], name := "(b, tau_a(c), a)",
      trip := function(T,G) return [E9[2], MiyTau(T,G,E9[1],E9[3]), E9[1]]; end,
      new := [2,0,0,1/2], rad := 5, case := "S3"),
  rec(par := [0,1,1,1/2], name := "(a, tau_c(b), c)",
      trip := function(T,G) return [E9[1], MiyTau(T,G,E9[3],E9[2]), E9[3]]; end,
      new := [2,1,1,3/2], rad := 5, case := "S3"),
  rec(par := [0,1,1,0], name := "(a, tau_c(b), c)",
      trip := function(T,G) return [E9[1], MiyTau(T,G,E9[3],E9[2]), E9[3]]; end,
      new := [4,1,1,2], rad := 3, case := "S1"),
  rec(par := [1,1,1,-1], name := "(a, tau_c(b), c)",
      trip := function(T,G) return [E9[1], MiyTau(T,G,E9[3],E9[2]), E9[3]]; end,
      new := [9,1,1,3], rad := 3, case := "S1")
];;

for C in Cases do
  P := C.par;
  T0 := MakeTable(P[1], P[2], P[3], P[4]);;
  G0 := MakeGram(P[1], P[2], P[3], P[4]);;
  x := C.trip(T0, G0);
  np := TripleParams(T0, G0, x);
  Print("\n(alpha,beta,gamma,psi) = ", P, ",  new triple ", C.name, "\n");
  Report("  dim A^perp", 9 - RankMat(G0) = C.rad);
  Report("  new axes are idempotents with (x,x) = 1",
    ForAll(x, y -> Same(Mult(T0,y,y), y) and Same(y*G0*y, 1)));
  Report("  psi' is well defined: (x1,x2x3) = (x2,x1x3) = (x3,x1x2)",
    Same(np[4], x[2]*G0*Mult(T0,x[1],x[3])) and Same(np[4], x[3]*G0*Mult(T0,x[1],x[2])));
  Report(Concatenation("  new parameters = ", String(C.new)), Same(np, C.new));
  Report("  first pair is toric: alpha' not in {0,1}", not np[1] in [0,1]);
  Report("  A is isomorphic to A(new parameters) via the new triple",
    IsIso(T0, TripleBasis(T0, x), MakeTable(np[1], np[2], np[3], np[4])));
  if C.case = "S3" then
    Report("  Theta' = 0 <> Sigma'  (case S3)", ThetaOf(np) = 0 and SigmaOf(np) <> 0);
    Report("  psi'^2 - alpha'beta'gamma' = 1/4 (a square)", -SigmaOf(np) = 1/4);
  else
    Report("  Sigma' = 0 <> Theta' and (beta',gamma',psi') <> 0  (case S1)",
      SigmaOf(np) = 0 and ThetaOf(np) <> 0 and np{[2..4]} <> [0,0,0]);
  fi;
od;

#############################################################################
Print("\n--- 3. Cross-check: all ideals over GF(p) by the MeatAxe ---\n");
##  By Lemma 3.5, ideals = subspaces invariant under ad_a, ad_b, ad_c.
##  Predicted dimensions of ideals: S3: [0,1,3,3,5,9];  S1: [0,3,9].
#############################################################################
IdealDims := function(P, p)
  local T0, one, mats, mdl;
  T0 := MakeTable(P[1], P[2], P[3], P[4]);
  one := One(GF(p));
  mats := List([1,2,3], k -> List([1..9], i -> T0[i][k]) * one);  # rows: e_i * x
  mdl := GModuleByMats(mats, GF(p));
  return SortedList(List(MTX.BasesSubmodules(mdl), Length));
end;;
Pred := rec(S3 := [0,1,3,3,5,9], S1 := [0,3,9]);;
for C in Cases do
  for p in [5, 7, 11, 13] do
    Report(Concatenation("  ", String(C.par), " over GF(", String(p), ")"),
      IdealDims(C.par, p) = Pred.(C.case));
  od;
od;
Print("\n  Characteristic 3 (reported, not predicted):\n");
for C in Cases do
  Print("  ", C.par, " over GF(3): ideal dimensions ", IdealDims(C.par, 3), "\n");
od;

#############################################################################
Print("\n--- 4. Characteristic 3: the Miyamoto closure of {a,b,c} ---\n");
#############################################################################
AxClosure := function(T0, G0, F0)
  local I9, AX, n, x, y, z;
  I9 := IdentityMat(9, F0);
  AX := [I9[1], I9[2], I9[3]];
  repeat
    n := Length(AX);
    for x in ShallowCopy(AX) do for y in ShallowCopy(AX) do
      z := MiyTau(T0, G0, x, y);
      if not z in AX then Add(AX, z); fi;
    od; od;
  until Length(AX) = n;
  return AX;
end;;
for P in [[0,1,1,0], [1,1,1,-1]] do
  one := One(GF(3));
  T3 := List(MakeTable(P[1],P[2],P[3],P[4]), r -> List(r, v -> v*one));
  G3 := MakeGram(P[1],P[2],P[3],P[4])*one;
  AX := AxClosure(T3, G3, GF(3));
  vals := Set(List(Combinations([1..Length(AX)], 2), ij -> AX[ij[1]]*G3*AX[ij[2]]));
  Print("  ", P, " over GF(3): ", Length(AX), " axes in the closure\n");
  Report("    all pairwise form values lie in {0,1} (no toric pair)",
    IsSubset([Zero(GF(3)), One(GF(3))], vals));
od;

Print("\nALL CHECKS PASSED: ", ForAll(results, x -> x = true), "\n");
