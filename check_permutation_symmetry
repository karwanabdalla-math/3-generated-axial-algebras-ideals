
#############################################################################
##  check_permutation_symmetry
##
##  Verifies that the universal algebra A(alpha,beta,gamma,psi) of
##  Gorshkov-Staroletov [J. Algebra 563 (2020), Table 1] is symmetric under
##  permutations of the generators a,b,c:
##
##    for every permutation s of {a,b,c}, the linear map phi_s sending
##      g_k        -> g_{s(k)}            (generators)
##      g_i g_j    -> g_{s(i)} g_{s(j)}   (products of two generators)
##      g_k(g_i g_j) -> g_{s(k)}(g_{s(i)} g_{s(j)})   (triple products)
##    is an algebra isomorphism A(P) -> A(P'), where P' is obtained from
##    P = (alpha,beta,gamma,psi) by moving each pair parameter
##    (g_i,g_j) to the pair (g_{s(i)},g_{s(j)}), and psi' = psi.
##
##  The parameters are indeterminates, so the check is symbolic (it holds
##  for all parameter values, over every field of characteristic not 2).
##
##  Basis order (as in [GS, Table 1]):
##    1:a  2:b  3:c  4:ab  5:bc  6:ac  7:a(bc)  8:b(ac)  9:c(ab)
#############################################################################

alpha := Indeterminate(Rationals, "alpha");;
beta  := Indeterminate(Rationals, "beta");;
gamma := Indeterminate(Rationals, "gamma");;
psi   := Indeterminate(Rationals, "psi");;

## Build a vector of length 9 from a list of [index, coefficient] pairs.
CURZERO := Zero(alpha);;
Vec := function(pairs)
  local v, pr;
  v := List([1..9], i -> CURZERO);
  for pr in pairs do
    v[pr[1]] := v[pr[1]] + pr[2];
  od;
  return v;
end;;

## Multiplication table of A(al,be,ga,ps) from [GS, Table 1].
## Returns a 9x9 matrix T whose entry T[i][j] is the vector e_i * e_j.
MakeTable := function(al, be, ga, ps)
  local T, S, a, b, c, ab, bc, ac, p, q, r;
  a:=1; b:=2; c:=3; ab:=4; bc:=5; ac:=6; p:=7; q:=8; r:=9;
  CURZERO := Zero(al);    # 0 for rational parameters, zero polynomial otherwise
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

  if ForAny(T, row -> ForAny(row, x -> x = fail)) then
    Error("multiplication table incomplete");
  fi;
  return T;
end;;

## Product of two vectors x, y in the algebra with table T.
Mult := function(T, x, y)
  local z, i, j;
  z := List([1..9], i -> Zero(T[1][1][1]));
  for i in [1..9] do
    if not IsZero(x[i]) then
      for j in [1..9] do
        if not IsZero(y[j]) then
          z := z + x[i]*y[j]*T[i][j];
        fi;
      od;
    fi;
  od;
  return z;
end;;

## Index of the product of generators i,j (as a set) and of the triple
## product with outer generator k.
PairIndex := function(i, j)
  local s; s := Set([i, j]);
  if s = [1,2] then return 4; elif s = [2,3] then return 5;
  elif s = [1,3] then return 6; fi;
end;;
TripleIndex := k -> 6 + k;;   # 7:a(bc), 8:b(ac), 9:c(ab)

## Basis map induced by a permutation s of {1,2,3}.
BasisImage := function(s)
  local img;
  img := [1^s, 2^s, 3^s,
          PairIndex(1^s, 2^s), PairIndex(2^s, 3^s), PairIndex(1^s, 3^s),
          TripleIndex(1^s), TripleIndex(2^s), TripleIndex(3^s)];
  return img;
end;;

## Transported parameters: pair {i,j} of the source carries the same value
## as pair {s(i),s(j)} of the target.
TargetParams := function(s)
  local val, pairs, src, P, k;
  # source values: {1,2}->alpha, {2,3}->beta, {1,3}->gamma
  src := [[[1,2], alpha], [[2,3], beta], [[1,3], gamma]];
  P := rec();
  for k in src do
    val := k[2];
    pairs := Set([k[1][1]^s, k[1][2]^s]);
    if pairs = [1,2] then P.al := val;
    elif pairs = [2,3] then P.be := val;
    else P.ga := val; fi;
  od;
  return [P.al, P.be, P.ga, psi];
end;;

ApplyMap := function(img, v)
  local w, i;
  w := List([1..9], i -> Zero(v[1]));
  for i in [1..9] do w[img[i]] := w[img[i]] + v[i]; od;
  return w;
end;;

CheckPermutation := function(s)
  local T, P2, T2, img, i, j, lhs, rhs, bad;
  T   := MakeTable(alpha, beta, gamma, psi);
  P2  := TargetParams(s);
  T2  := MakeTable(P2[1], P2[2], P2[3], P2[4]);
  img := BasisImage(s);
  bad := 0;
  for i in [1..9] do
    for j in [1..9] do
      # phi(e_i e_j)  versus  phi(e_i) * phi(e_j) in the target algebra
      lhs := ApplyMap(img, T[i][j]);
      rhs := T2[img[i]][img[j]];
      if lhs <> rhs then
        bad := bad + 1;
        Print("  mismatch at (", i, ",", j, ")\n");
      fi;
    od;
  od;
  return bad;
end;;

## Sanity check of the table itself, at random rational parameter values:
## the Jordan identity (x^2 y) x = x^2 (y x) on random elements, and the
## eigenspace dimensions of ad_a.
SanityCheck := function()
  local T, x, y, x2, ok, k, al, be, ga, ps, M;
  ok := true;
  for k in [1..5] do
    al := Random([-20..20])/Random([1..9]);
    be := Random([-20..20])/Random([1..9]);
    ga := Random([-20..20])/Random([1..9]);
    ps := Random([-20..20])/Random([1..9]);
    T := MakeTable(al, be, ga, ps);
    x := List([1..9], i -> Random([-5..5]));
    y := List([1..9], i -> Random([-5..5]));
    x2 := Mult(T, x, x);
    if Mult(T, Mult(T, x2, y), x) <> Mult(T, x2, Mult(T, y, x)) then
      ok := false;
    fi;
    # ad_a must have eigenvalues 1,0,1/2 with multiplicities 1,4,4
    M := List([1..9], j -> T[1][j]);   # rows: a*e_j
    # ad_a is diagonalizable with eigenvalues 1,0,1/2 of multiplicities 1,4,4
    # iff these three nullities are 1,4,4 (they then add up to 9)
    if RankMat(M) <> 5 or RankMat(M - IdentityMat(9)) <> 8
       or RankMat(M - (1/2)*IdentityMat(9)) <> 5 then
      ok := false;
    fi;
  od;
  return ok;
end;;

#############################################################################
Print("Sanity check of [GS, Table 1] (Jordan identity, spectrum of ad_a): ",
      SanityCheck(), "\n\n");

for s in Elements(SymmetricGroup(3)) do
  Print("Permutation ", s, ": generators a,b,c -> ",
        List([1,2,3], k -> ["a","b","c"][k^s]),
        ", parameters (alpha,beta,gamma,psi) -> ", TargetParams(s), "\n");
  Print("  number of mismatches: ", CheckPermutation(s), "\n");
od;
Print("\nAll 6 permutations checked on all 81 products of basis elements.\n");
