#############################################################################
##  check_Section_6_3.g
##
##  Verification of Section 6.3 (the algebra (0,0,0,0)) in the paper on
##  ideals in 3-generated primitive axial algebras of Jordan type 1/2:
##    - A^perp = <ab, ac, bc, p, q, r>, and p, q, r in terms of u1, u2, u3;
##    - the action of a, b, c on u1, u2, u3 and on ab, ac, bc;
##    - the ideals N^ab_[lambda:mu], symbolically in lambda, mu
##      (N^ac and N^bc follow by symmetry, Remark 2.21);
##    - the block I_a = <a, ab, ac> + U, using 4 aq - q + r = p;
##    - Remark 6.13: the number of ideals is 3q + 25 over GF(5) and GF(7),
##      with 1, 3, 3, 3q+1, 3, 3, 4, 3, 3, 1 ideals of dimensions 0, ..., 9.
##
##  Basis order as in [GS, Table 1] and check_main.g:
##    1:a  2:b  3:c  4:ab  5:bc  6:ac  7:p=a(bc)  8:q=b(ac)  9:r=c(ab)
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




Print("\n--- Section 6.3: the algebra (0,0,0,0) ---\n");
E9 := IdentityMat(9, Rationals);;
a := E9[1];; b := E9[2];; c := E9[3];; ab := E9[4];; bc := E9[5];; ac := E9[6];;
p := E9[7];; q := E9[8];; r := E9[9];;
IsPow2 := n -> n <> 0 and ForAll(Factors(AbsInt(n)), x -> x = 2);;
InZhalf := x -> IsRat(x) and (DenominatorRat(x) = 1 or IsPow2(DenominatorRat(x)));;
RankOverZhalf := function(Bs)
  local ed;
  Bs := Bs * Lcm(List(Flat(Bs), DenominatorRat));
  ed := Filtered(ElementaryDivisorsMat(Bs), d -> d <> 0);
  if ForAll(ed, d -> d = 1 or IsPow2(d)) then return Length(ed); fi;
  return fail;
end;;


one := 0;; mats := 0;; dims := 0;;
T0 := MakeTable(0,0,0,0);;  G0 := MakeGram(0,0,0,0);;
M := function(x, y) return Mult(T0, x, y); end;;
AXES := [a, b, c];;
u1 := p+q-r;; u2 := p-q+r;; u3 := -p+q+r;;
Report("A^perp = <ab,ac,bc,p,q,r>",
  RankMat(NullspaceMat(G0)) = 6 and ForAll([ab,ac,bc,p,q,r], v -> IsZero(v*G0)));
Report("p = (u1+u2)/2, q = (u1+u3)/2, r = (u2+u3)/2",
  p = (u1+u2)/2 and q = (u1+u3)/2 and r = (u2+u3)/2);
Report("characters of u1,u2,u3: (1/2,1/2,0), (1/2,0,1/2), (0,1/2,1/2)",
  List(AXES, x -> M(x,u1)) = [u1/2, u1/2, 0*u1] and
  List(AXES, x -> M(x,u2)) = [u2/2, 0*u2, u2/2] and
  List(AXES, x -> M(x,u3)) = [0*u3, u3/2, u3/2]);
Report("ab: a ab = b ab = ab/2, c ab = r",
  M(a,ab) = ab/2 and M(b,ab) = ab/2 and M(c,ab) = r);
Report("ac: a ac = c ac = ac/2, b ac = q",
  M(a,ac) = ac/2 and M(c,ac) = ac/2 and M(b,ac) = q);
Report("bc: b bc = c bc = bc/2, a bc = p",
  M(b,bc) = bc/2 and M(c,bc) = bc/2 and M(a,bc) = p);
## the family N^ab_[lambda:mu], symbolically in lambda, mu
la := Indeterminate(Rationals, "lambda");; mu := Indeterminate(Rationals, "mu");;
xv := mu*ab + la*u1;;
Report("N^ab_[lambda:mu] = <mu ab + lambda u1, u2, u3> is stable under a, b, c",
  M(a,xv) = xv/2 and M(b,xv) = xv/2 and M(c,xv) = mu*(u2+u3)/2);
## the block I_a
Ia := [a, ab, ac, p, q, r];;
Report("I_a = <a,ab,ac,p,q,r> is stable under a, b, c",
  ForAll(AXES, x -> ForAll(Ia, v -> SolutionMat(Ia, M(x,v)) <> fail)));
Report("I_a contains ab, ac, q = b(ac), r = c(ab), and p = 4 aq - q + r",
  M(b,a) = ab and M(c,a) = ac and M(b,ac) = q and M(c,ab) = r
  and M(a,q) = (p+q-r)/4);
## Remark 6.13: number of ideals of each dimension over GF(5) and GF(7)
for pr in [5, 7] do
  one := One(GF(pr));
  mats := List([1,2,3], k -> List([1..9], i -> T0[i][k]) * one);
  dims := List(MTX.BasesSubmodules(GModuleByMats(mats, GF(pr))), Length);
  Report(Concatenation("number of ideals by dimension over GF(", String(pr), ")"),
    List([0..9], d -> Number(dims, x -> x = d)) = [1,3,3,1+3*pr,3,3,4,3,3,1]);
od;
Print("\nALL CHECKS PASSED: ", ForAll(results, x -> x = true), "\n");
