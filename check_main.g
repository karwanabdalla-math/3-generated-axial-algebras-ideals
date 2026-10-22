#############################################################################
##  check_main.g
###
##  Symbolic verification of the computations in Sections 3 and 4.1-4.3
##  of the paper on ideals in 3-generated primitive axial algebras of
##  Jordan type 1/2.  Part 0 checks the transcription of [GS, Tables 1
##  and 5] (Table 1 of the paper) via the Frobenius property; Parts 1-5
##  cover Section 3.1; Parts 6-15 cover Sections 3.4-3.7 and 4.1-4.3.
##  Section 4.4 is verified in check_hidden_toric.g, Example 4.5 in
##  check_Remark_3_21.g, and Section 5 in check_Section_5_*.g.
##
##  Parameters: zeta, beta, gamma, psi are indeterminates, and
##      alpha = (zeta+1)^2/(4 zeta),
##  so every check holds identically, for all parameter values
##  (with zeta <> 0, +-1), over every field of characteristic not 2.
##
##  Normalization (as in the paper):  a = d_1,  b = d_{1/zeta},
##  where d_xi = xi*s + (1/2)*1_B + xi^(-1)*t.
##
##  Basis order of A (as in [GS, Table 1]):
##    1:a  2:b  3:c  4:ab  5:bc  6:ac  7:p=a(bc)  8:q=b(ac)  9:r=c(ab)
##  The basis E = (e1,...,e6) of W = B^perp in the paper is
##    e1=c°, e2=(bc)°, e3=(ac)°, e4=p°, e5=q°, e6=r°,
##  so the E-coordinates of w in W are its entries at positions
##    [3,5,6,7,8,9].
#############################################################################

zeta  := Indeterminate(Rationals, "zeta");;
beta  := Indeterminate(Rationals, "beta");;
gamma := Indeterminate(Rationals, "gamma");;
psi   := Indeterminate(Rationals, "psi");;
alpha := (zeta+1)^2/(4*zeta);;
xx    := Indeterminate(Rationals, "x");;     # x/y for points [x:y]
yy    := Indeterminate(Rationals, "y");;     # y, for homogeneous forms
xi    := Indeterminate(Rationals, "xi");;    # torus parameter of c_B

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


T := MakeTable(alpha, beta, gamma, psi);;
Z9 := List([1..9], i -> Zero(alpha));;
E9 := function(i) local v; v := ShallowCopy(Z9); v[i] := One(alpha); return v; end;;
M  := function(x, y) return Mult(T, x, y); end;;

#############################################################################
##  The normalized Frobenius form, from [GS, Table 5] (Gram matrix on the
##  basis above).  Its associativity is verified below, which also checks
##  the transcription.
#############################################################################
al:=alpha;; be:=beta;; ga:=gamma;; ps:=psi;;
G := NullMat(9, 9, Zero(alpha));;
SetG := function(i, j, v) G[i][j] := v; G[j][i] := v; end;;
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
Form := function(x, y) return x*G*y; end;;

## Robust equality: GAP may store a zero rational function as e.g. 0/(zeta+1),
## so we test equality as "difference is zero", entrywise.
Same := function(x, y)
  if IsList(x) then
    return Length(x) = Length(y) and ForAll([1..Length(x)], i -> Same(x[i], y[i]));
  fi;
  return IsZero(x - y);
end;;

results := [];;
Report := function(name, ok)
  Add(results, ok);
  Print(String(name, -62), " ", ok, "\n");
end;;

Print("\n--- 0. Frobenius form ---\n");
Report("(e_i e_j, e_k) = (e_i, e_j e_k) for all 729 triples",
  ForAll(Cartesian([1..9],[1..9],[1..9]), t ->
    Same(Form(T[t[1]][t[2]], E9(t[3])), Form(E9(t[1]), T[t[2]][t[3]]))));
Report("(a,a) = (b,b) = (c,c) = 1",
  ForAll([1,2,3], i -> Same(G[i][i], 1)));

#############################################################################
Print("\n--- 1. The toric basis {s, 1_B, t} of B (Proposition 2.24) ---\n");
#############################################################################
a := E9(1);; b := E9(2);; c := E9(3);; ab := E9(4);;
one := (2/(alpha-1)) * (ab - a/2 - b/2);;          # 1_B
Report("1_B is the identity of B (1_B a = a, 1_B b = b)",
  Same(M(one,a), a) and Same(M(one,b), b));
# a = d_1 = s + 1_B/2 + t,  b = d_{1/zeta} = s/zeta + 1_B/2 + zeta*t
X0 := a - one/2;;  Y0 := b - one/2;;
s := (Y0 - zeta*X0) / (1/zeta - zeta);;
t := X0 - s;;
Report("s^2 = 0, t^2 = 0, st = 1_B/8",
  Same(M(s,s), Z9) and Same(M(t,t), Z9) and Same(M(s,t), one/8));
Report("a = d_1 and b = d_(1/zeta)",
  Same(a, s + one/2 + t) and Same(b, s/zeta + one/2 + zeta*t));
Report("Gram(s,1_B,t) = [[0,0,1/4],[0,2,0],[1/4,0,0]]",
  Same([[Form(s,s),Form(s,one),Form(s,t)],
   [Form(one,s),Form(one,one),Form(one,t)],
   [Form(t,s),Form(t,one),Form(t,t)]], [[0,0,1/4],[0,2,0],[1/4,0,0]]));
Report("alpha = (a,b) = (zeta+1)^2/(4 zeta)", Same(Form(a,b), alpha));

#############################################################################
Print("\n--- 2. The basis E of W = B^perp ---\n");
#############################################################################
Bb := [a, b, ab];;
GB := List(Bb, x -> List(Bb, y -> Form(x,y)));;
GBinv := GB^-1;;
ProjW := function(x)          # x - pi_B(x)
  local rhs, co;
  rhs := List(Bb, y -> Form(x,y));
  co  := GBinv * rhs;
  return x - co[1]*Bb[1] - co[2]*Bb[2] - co[3]*Bb[3];
end;;
WBasis := List([3,5,6,7,8,9], i -> ProjW(E9(i)));;     # e1..e6
Report("e_i is orthogonal to B (i = 1..6)",
  ForAll(WBasis, e -> ForAll(Bb, x -> Same(Form(e,x), 0))));
WPOS := [3,5,6,7,8,9];;
Coords := w -> w{WPOS};;                           # E-coordinates of w in W
FromCoords := co -> co * WBasis;;
Report("B W is contained in W",
  ForAll(Bb, x -> ForAll(WBasis, e -> Same(FromCoords(Coords(M(x,e))), M(x,e)))));

# matrices of omega = ad_s|W and chi = ad_t|W (columns = images of e_j)
MatOf := x -> TransposedMat(List(WBasis, e -> Coords(M(x,e))));;
Om := MatOf(s);;  Ch := MatOf(t);;  Id6 := IdentityMat(6, alpha);;
Report("omega^2 = 0 and chi^2 = 0",
  Same(Om*Om, NullMat(6,6,Zero(alpha))) and Same(Ch*Ch, NullMat(6,6,Zero(alpha))));
Report("rank omega = rank chi = 2", RankMat(Om) = 2 and RankMat(Ch) = 2);
Dbasis := NullspaceMat(TransposedMat(Concatenation(Om, Ch)));;
Report("dim D = dim(ker omega cap ker chi) = 2", Length(Dbasis) = 2);
ImOm := BaseMat(TransposedMat(Om));;  ImCh := BaseMat(TransposedMat(Ch));;
Report("W = im omega + D + im chi (direct, total dimension 6)",
  RankMat(Concatenation(ImOm, Dbasis, ImCh)) = 6);
Report("omega(chi(x)) = x/16 for x in im omega",
  ForAll(ImOm, x -> Same(Om*(Ch*x), x/16)));
Report("chi(omega(y)) = y/16 for y in im chi",
  ForAll(ImCh, y -> Same(Ch*(Om*y), y/16)));

#############################################################################
Print("\n--- 3. Lemma 3.2 (basis of D, action of 1_B) ---\n");
#############################################################################
k := 2/(alpha-1);;
d1 := One(alpha)*[1, k, k, -2*k, -2*k, 0];;   d2 := One(alpha)*[0, 0, 0, 1, 1, -1];;
Report("omega(d_i) = chi(d_i) = 0 (i = 1,2)",
  ForAll([d1,d2], d -> Same(Om*d, 0*d) and Same(Ch*d, 0*d)));
Report("d1, d2 linearly independent", RankMat([d1,d2]) = 2);
Ad := x -> MatOf(x);;
Report("a d1 = -(k/2) d2  and  a d2 = d2/2",
  Same(Ad(a)*d1, -(k/2)*d2) and Same(Ad(a)*d2, d2/2));
Report("1_B d1 = -k d2  and  1_B d2 = d2",
  Same(Ad(one)*d1, -k*d2) and Same(Ad(one)*d2, d2));
Report("1_B (d1 + k d2) = 0", Same(Ad(one)*(d1 + k*d2), 0*d1));

#############################################################################
Print("\n--- 4. The bases of X = im omega and Y = im chi ---\n");
#############################################################################
mu := -(zeta+1)/4;;  nu := -(zeta+1)/(4*zeta);;
u1 := One(alpha)*[0, nu, mu, 0, 0, 1];;
u2 := One(alpha)*[0, -(mu-nu), 0, -zeta, -1, 1];;
v1 := One(alpha)*[0, -1/4, -1/4, 1/(zeta+1), zeta/(zeta+1), 0];;
v2 := One(alpha)*[0, (zeta-1)/4, 0, 1/(zeta+1), zeta/(zeta+1), -zeta/(zeta+1)];;
Report("u1, u2 lie in X = im omega and are independent",
  RankMat(Concatenation(ImOm, [u1,u2])) = 2 and RankMat([u1,u2]) = 2);
Report("chi(u_i) = nu * v_i (i = 1,2)",
  Same(Ch*u1, nu*v1) and Same(Ch*u2, nu*v2));
Report("v1, v2 lie in Y = im chi and are independent",
  RankMat(Concatenation(ImCh, [v1,v2])) = 2 and RankMat([v1,v2]) = 2);

#############################################################################
Print("\n--- 5. Proposition 3.3 (Peirce decomposition of W) ---\n");
#############################################################################
Report("1_B u = u/2 for u in {u1, u2, v1, v2}",
  ForAll([u1,u2,v1,v2], u -> Same(Ad(one)*u, u/2)));
Report("W = D0 + D1 + U with D0=<d1+k d2>, D1=<d2>, U=<u1,u2,v1,v2>",
  RankMat([d1 + k*d2, d2, u1, u2, v1, v2]) = 6);


ThetaP := alpha + beta + gamma - 2*psi - 1;;
SigmaP := alpha*beta*gamma - psi^2;;
Subs := function(f, vals)          # substitute (beta,gamma,psi) := vals
  return Value(f, [beta, gamma, psi], vals);
end;;
SubsV := function(v, vals) return List(v, f -> Subs(f, vals)); end;;
CW := MatOf(c);;                                 # matrix of C_W (columns)
CWapply := w -> CW * w;;
PhiW := w -> 8*zeta*w[1] + 4*zeta*(w[2]+w[3]) + 2*zeta*(w[4]+w[5])
            + (zeta+1)^2*w[6];;
ell := w -> 4*zeta*(w[2]+w[3]) + 2*zeta*(w[4]+w[5]) + (zeta+1)^2*w[6];;
g := d1 + k*d2;;
# Gamma on the stratum Theta = 0
gamTh0 := 1 - alpha - beta + 2*psi;;

#############################################################################
Print("\n--- 6. Lemma 3.13 and Remark 3.14 (the B-component c_B) ---\n");
#############################################################################
cB := c - ProjW(c);;
Report("c_B = formula of Lemma 3.13",
  Same(cB, ((gamma+alpha*beta-2*psi)/(alpha-1)^2)*a
         + ((beta+alpha*gamma-2*psi)/(alpha-1)^2)*b
         + (2*((alpha+1)*psi-alpha*(beta+gamma))/(alpha*(alpha-1)^2))*ab));
Report("det Gram(a,b,ab) = -alpha(alpha-1)^3/2",
  Same(DeterminantMat(GB), -alpha*(alpha-1)^3/2));
NNc := Form(one, c);;
Report("c_B = 4(t,c) s + (N/2) 1_B + 4(s,c) t",
  Same(cB, 4*Form(t,c)*s + (NNc/2)*one + 4*Form(s,c)*t));
Report("N = (2 psi - beta - gamma)/(alpha-1)",
  Same(NNc, (2*psi-beta-gamma)/(alpha-1)));
Report("Theta = (alpha-1)(1-N)", Same(ThetaP, (alpha-1)*(1-NNc)));

#############################################################################
Print("\n--- 7. Lemma 3.15 (the six formulas for C_W) ---\n");
#############################################################################
F := List([1..6], i -> 0*d1);;
F[1] := One(alpha)*[1, -(beta+alpha*gamma-2*psi)/(alpha-1)^2,
        -(gamma+alpha*beta-2*psi)/(alpha-1)^2, 0, 0,
        2*(alpha*(beta+gamma)-(alpha+1)*psi)/(alpha*(alpha-1)^2)];;
F[2] := One(alpha)*[beta/2, (alpha+2*beta-2*psi-1)/(2*(alpha-1)), 0, 0, 0,
        -(alpha*beta-psi)/(alpha*(alpha-1))];;
F[3] := One(alpha)*[gamma/2, 0, (alpha+2*gamma-2*psi-1)/(2*(alpha-1)), 0, 0,
        -(alpha*gamma-psi)/(alpha*(alpha-1))];;
F[4] := One(alpha)*[psi/4, gamma/4, -(alpha*beta+beta-2*psi)/(4*(alpha-1)),
        1/4, -1/4, (alpha^2+2*alpha*beta-4*alpha*psi-alpha+2*psi)/(4*alpha*(alpha-1))];;
F[5] := One(alpha)*[psi/4, -(alpha*gamma+gamma-2*psi)/(4*(alpha-1)), beta/4,
        -1/4, 1/4, (alpha^2+2*alpha*gamma-4*alpha*psi-alpha+2*psi)/(4*alpha*(alpha-1))];;
F[6] := One(alpha)*[psi/2, -(alpha*gamma-psi)/(2*(alpha-1)),
        -(alpha*beta-psi)/(2*(alpha-1)), 0, 0, ThetaP/(2*(alpha-1))];;
Report("C_W(e_i) agrees with Lemma 3.15 for i = 1..6",
  ForAll([1..6], i -> Same(CW*IdentityMat(6,alpha)[i], F[i])));
Report("eq. (1): e4,e5-coordinates of C_W(w) are (w4-w5)/4, -(w4-w5)/4",
  ForAll([1..6], i -> Same(CW[4][i], [0,0,0,1/4,-1/4,0][i])
                  and Same(CW[5][i], [0,0,0,-1/4,1/4,0][i])));

#############################################################################
Print("\n--- 8. Proposition 3.16, Remark 3.17, Lemma 3.11 ---\n");
#############################################################################
Report("C_W(g) = Theta/(alpha-1) e1 + Theta/(alpha-1)^2 (e2+e3-2e6)",
  Same(CW*g, (ThetaP/(alpha-1))*[1,0,0,0,0,0]
            + (ThetaP/(alpha-1)^2)*[0,1,1,0,0,-2]));
Report("C_W(d2) = (gamma/2) e2 + (beta/2) e3 - (psi/alpha) e6",
  Same(CW*d2, [0, gamma/2, beta/2, 0, 0, -psi/alpha]));
Report("C_W(d1) = e1 + (k/2)(e2+e3) - k e6  when beta=gamma=psi=0",
  Same(SubsV(CW*d1, [0,0,0]), SubsV(One(alpha)*[1,k/2,k/2,0,0,-k],[0,0,0])));
# Lemma 3.11 / C_B: for w in W, C_B(w)=0 iff (w,e2)=(w,e3)=(w,e6)=0
gvec := FromCoords(g);;
Report("Theta=0:  A g = 0 (Remark 3.17)",
  ForAll([1..9], i -> Same(SubsV(M(E9(i), gvec), [beta,gamTh0,psi]), Z9)));
d2vec := FromCoords(d2);;
Report("beta=gamma=psi=0:  (d2,e2)=(d2,e3)=(d2,e6)=0, so C_B(d2)=0",
  ForAll([2,3,6], i -> Same(Subs(Form(d2vec, WBasis[i]),[0,0,0]), 0)));
Report("Lemma 3.11: C_B(w) is determined by (w,e2),(w,e3),(w,e6)",
  ForAll(WBasis, w -> Same(Form(M(c,w), a), Form(w, WBasis[3]))
                  and Same(Form(M(c,w), b), Form(w, WBasis[2]))
                  and Same(Form(M(c,w), ab), Form(w, WBasis[6]))));

#############################################################################
Print("\n--- 9. Propositions 3.18-3.22 and 3.26-3.29: C_W-stability ---\n");
##  For a candidate I (with x = xx, y = 1), the condition C_W(I) <= I is
##  affine-linear in (beta,gamma,psi).  We compute that linear system and
##  compare its solution set with the condition stated in the paper.
#############################################################################
hX := zeta - 1 - xx;;                               # h for y = 1
uX := xx*u1 + u2;;   vX := xx*v1 + v2;;
LinRows := function(gens)
  local ann, rows, w, phi, f, f0;
  ann := NullspaceMat(TransposedMat(gens));
  rows := [];
  for w in gens do
    for phi in ann do
      f := phi * (CW * w);
      f0 := Subs(f, [0,0,0]);
      Add(rows, One(alpha)*[Subs(f,[1,0,0]) - f0, Subs(f,[0,1,0]) - f0,
                 Subs(f,[0,0,1]) - f0, f0]);
      # check affine-linearity in (beta, gamma, psi)
      if not Same(f, rows[Length(rows)]*[beta,gamma,psi,1]) then
        Error("not affine-linear");
      fi;
    od;
  od;
  return rows;
end;;
# Compare two affine systems (rows [cb,cg,cp,c0]): same solution set
SameSystem := function(R1, R2)
  local r1, r2, r12;
  R1 := One(alpha)*R1;  R2 := One(alpha)*R2;
  r1 := RankMat(R1);  r2 := RankMat(R2);
  r12 := RankMat(Concatenation(R1, R2));
  return r1 = r2 and r1 = r12;
end;;
# Stated conditions, as affine rows in (beta,gamma,psi | 1):
ThRow := One(alpha)*[1, 1, -2, alpha-1];;                       # Theta = 0
MRows := One(alpha)*[[4*(xx+1), 0, 0, xx^2],                       # Prop 3.18
                     [0, 4*zeta*(xx+1), 0, hX^2],
                     [0, 0, 8*zeta*(xx+1), -xx*(zeta+1)*hX]];;
D1MRows := One(alpha)*[[(zeta+1)*hX, 0, 2*zeta*xx, 0],           # eq. (2)
                       [0, (zeta+1)*xx, 2*hX, 0]];;
QRow := One(alpha)*[2*((xx+1)^2 - zeta^2), -2*zeta*xx*(xx+2), 0,
                    -xx*(zeta-1)*hX];;                             # Q = 0
ZeroRows := One(alpha)*[[1,0,0,0],[0,1,0,0],[0,0,1,0]];;          # b=g=p=0
Report("M_[x:y]:            C_W-stable  <=>  relations of Prop 3.18",
  SameSystem(LinRows([uX, vX]), MRows));
Report("D1+M_[x:y]:         C_W-stable  <=>  eq. (2)",
  SameSystem(LinRows([d2, uX, vX]), D1MRows));
Report("D0+M_[x:y]:         C_W-stable  <=>  Theta = 0 and Q = 0",
  SameSystem(LinRows([g, uX, vX]), [ThRow, QRow]));
Report("D0+D1+M_[x:y]:      C_W-stable  <=>  relations of Prop 3.18",
  SameSystem(LinRows([d1, d2, uX, vX]), MRows));
Report("D0:                 C_W-stable  <=>  Theta = 0",
  SameSystem(LinRows([g]), [ThRow]));
Report("D1:                 C_W-stable  <=>  beta = gamma = psi = 0",
  SameSystem(LinRows([d2]), ZeroRows));
Report("D1+U:               C_W-stable  <=>  beta = gamma = psi = 0",
  SameSystem(LinRows([d2,u1,u2,v1,v2]), ZeroRows));
Report("D0+U:               C_W-stable  <=>  Theta = 0",
  SameSystem(LinRows([g,u1,u2,v1,v2]), [ThRow]));
Report("U:                  never C_W-stable (inconsistent system)",
  RankMat(LinRows([u1,u2,v1,v2])) > RankMat(List(LinRows([u1,u2,v1,v2]), r -> r{[1..3]})));
Report("D0+D1:              never C_W-stable (inconsistent system)",
  RankMat(LinRows([d1,d2])) > RankMat(List(LinRows([d1,d2]), r -> r{[1..3]})));
Report("identity (4): Phi(C_W(w)) = Phi(w)/2 + Theta(4z/(a-1) w1 + z w4 + z w5)",
  ForAll(IdentityMat(6,alpha), w -> Same(PhiW(CW*w),
     PhiW(w)/2 + ThetaP*(4*zeta/(alpha-1)*w[1] + zeta*w[4] + zeta*w[5]))));
Report("ell(C_W(u2)) = -(zeta-1)^2(zeta+1)/4 when beta=gamma=psi=0",
  Same(Subs(ell(CW*u2),[0,0,0]), -(zeta-1)^2*(zeta+1)/4));
Report("Prop 3.19: det of eq. (2) in variables (x,h) is -4 zeta Sigma",
  Same(DeterminantMat([[2*zeta*psi, beta*(zeta+1)],[gamma*(zeta+1), 2*psi]]),
       -4*zeta*SigmaP));

#############################################################################
Print("\n--- 10. The B-component: Proposition 3.23 and Lemma 3.24 ---\n");
##  C_B(W) = 0  iff  (w, e_i) = 0 for all w in W and i in {2,3,6}.
##  The Gram entries (e_i, e_j), i in {2,3,6}, are quadratic in
##  (beta,gamma,psi); we show they span the same space as
##  Sigma, beta*Theta, gamma*Theta, psi*Theta.
#############################################################################
GW := List(WBasis, x -> List(WBasis, y -> Form(x,y)));;
QuadCoeffs := function(f)        # coefficients of a quadratic in (b,g,p)
  local c0, ci, cii, cij, i, j, e, rec1, v;
  e := IdentityMat(3);
  c0 := Subs(f, [0,0,0]);
  cii := List([1..3], i -> (Subs(f, 2*e[i]) - 2*Subs(f, e[i]) + c0)/2);
  ci  := List([1..3], i -> Subs(f, e[i]) - c0 - cii[i]);
  cij := List([[1,2],[1,3],[2,3]], p -> Subs(f, e[p[1]]+e[p[2]]) - c0
              - ci[p[1]] - ci[p[2]] - cii[p[1]] - cii[p[2]]);
  v := Concatenation([c0], ci, cii, cij);
  rec1 := c0 + ci*[beta,gamma,psi] + cii*[beta^2,gamma^2,psi^2]
          + cij*[beta*gamma, beta*psi, gamma*psi];
  if not Same(f, rec1) then Error("not quadratic"); fi;
  return v;
end;;
Entries := List(Cartesian([2,3,6],[1..6]), p -> QuadCoeffs(GW[p[1]][p[2]]));;
Targets := List([SigmaP, beta*ThetaP, gamma*ThetaP, psi*ThetaP], QuadCoeffs);;
Report("Lemma 3.11 reformulated: (C_B(w), b0) = (w, pi_W(c b0)) on W",
  ForAll(WBasis, w -> ForAll(Bb, x -> Same(Form(M(c,w),x),
                                         Form(w, ProjW(M(c,x)))))));
Report("Prop 3.23: span{(e_i,e_j): i in {2,3,6}} = span{Sigma, b.Th, g.Th, p.Th}",
  RankMat(Entries) = 4 and RankMat(Targets) = 4
  and RankMat(Concatenation(Entries, Targets)) = 4);
CBof := w -> M(c, w) - ProjW(M(c, w));;             # pi_B(c w)
Report("Lemma 3.24: Theta=0 => C_B(w) = -2 zeta Sigma/(zeta^2-1)^2 Phi(w) 1_B",
  ForAll([1..6], i -> Same(SubsV(CBof(WBasis[i]), [beta,gamTh0,psi]),
      SubsV((-2*zeta*SigmaP/(zeta^2-1)^2) * PhiW(IdentityMat(6,alpha)[i]) * one,
            [beta,gamTh0,psi]))));

#############################################################################
Print("\n--- 11. C_B on the claimed loci (sufficiency in Props 3.18-3.22) ---\n");
#############################################################################
CBzero := function(gens, vals)
  return ForAll(gens, w -> Same(SubsV(CBof(FromCoords(w)), vals), Z9));
end;;
Mvals := [-xx^2/(4*(xx+1)), -hX^2/(4*zeta*(xx+1)), (zeta+1)*xx*hX/(8*zeta*(xx+1))];;
Report("Prop 3.18: C_B(M_[x:y]) = 0 on its locus", CBzero([uX,vX], Mvals));
Report("Prop 3.18: Theta = Sigma = 0 on its locus",
  Same(Subs(ThetaP, Mvals), 0) and Same(Subs(SigmaP, Mvals), 0));
Report("Prop 3.22: eq. (2) holds on the locus of Prop 3.18",
  ForAll(D1MRows, r -> Same(r*Concatenation(Mvals,[1]), 0)));
Report("Prop 3.22: Q = 0 on the locus of Prop 3.18",
  Same(QRow*Concatenation(Mvals,[1]), 0));
D1Mvals := [zeta*gamma*xx^2/hX^2, gamma, -gamma*(zeta+1)*xx/(2*hX)];;
Report("Prop 3.19: C_B(D1+M_[x:y]) = 0 on eq. (2) (gamma free)",
  CBzero([d2,uX,vX], D1Mvals));
# Theta = 0 and Q = 0: solve for (beta, gamma) with psi free
sol := SolutionMat(TransposedMat([ThRow{[1,2]}, QRow{[1,2]}]),
        -[ThRow[3]*psi + ThRow[4], QRow[3]*psi + QRow[4]]);;
D0Mvals := [sol[1], sol[2], psi];;
Report("Prop 3.20: C_B(D0+M_[x:y]) = 0 on Theta = Q = 0",
  CBzero([g,uX,vX], D0Mvals));
Report("Prop 3.28: C_B(D0+U) = 0 on Theta = 0",
  CBzero([g,u1,u2,v1,v2], [beta,gamTh0,psi]));
Report("Prop 3.27: C_B(W) = 0 when beta = gamma = psi = 0",
  CBzero(IdentityMat(6,alpha), [0,0,0]));

#############################################################################
Print("\n--- 12. Remark 3.21 (the quadratic form Q under Theta = 0) ---\n");
#############################################################################
hXY := yy*(zeta-1) - xx;;
Qh := 2*((xx+yy)^2 - zeta^2*yy^2)*beta - 2*zeta*xx*(xx+2*yy)*gamTh0 - xx*(zeta-1)*hXY;;
A2 := Value(Qh, [xx,yy], [1,0]);;  A0 := Value(Qh, [xx,yy], [0,1]);;
A1 := Value(Qh, [xx,yy], [1,1]) - A2 - A0;;
Report("Q is a binary quadratic form (Q = A2 x^2 + A1 xy + A0 y^2)",
  Same(Qh, A2*xx^2 + A1*xx*yy + A0*yy^2));
Report("discriminant A1^2 - 4 A2 A0 = -64 zeta^2 Sigma = (8 zeta)^2 (psi^2 - alpha beta gamma)",
  Same(A1^2 - 4*A2*A0, -64*zeta^2*Subs(SigmaP, [beta,gamTh0,psi])));
Report("Q never identically 0: A0 = 2 beta (1-zeta^2), and A1 - 2 A2 = -(zeta^2-1) at beta = 0",
  Same(A0, 2*beta*(1-zeta^2)) and Same(Subs(A1 - 2*A2, [0,gamma,psi]), -(zeta^2-1)));

#############################################################################
Print("\n--- 13. Lemma 4.1 (intrinsic form) ---\n");
#############################################################################
PPc := Form(s,c)*Form(t,c);;
Report("Sigma = alpha(alpha-1)(16 P - N^2)/4",
  Same(SigmaP, alpha*(alpha-1)*(16*PPc - NNc^2)/4));
Report("c_B^2 = N c_B + (4P - N^2/4) 1_B",
  Same(M(cB,cB), NNc*cB + (4*PPc - NNc^2/4)*one));
Report("d_xi = xi s + 1_B/2 + t/xi is an idempotent of B (Prop 2.24)",
  Same(M(xi*s + one/2 + t/xi, xi*s + one/2 + t/xi), xi*s + one/2 + t/xi));

#############################################################################
Print("\n--- 14. Lemma 4.2 and Example 4.4 ---\n");
#############################################################################
pairing := function(p, q) return (p+q)^2/(4*p*q); end;;
bxi := pairing(1/zeta, xi);;  gxi := pairing(1, xi);;
pxi := (bxi + gxi + alpha - 1)/2;;
Xxi := -(1 + zeta*xi);;
Report("torus parameters satisfy Theta = Sigma = 0",
  Same(Value(Subs(ThetaP,[bxi,gxi,pxi]),[xx],[Xxi]), 0)
  and Same(Subs(SigmaP,[bxi,gxi,pxi]), 0));
Report("Lemma 4.2: relations of Prop 3.18 hold at [x:y] = [-(1+zeta xi):1]",
  ForAll([1..3], i -> Same(Value(Mvals[i],[xx],[Xxi]), [bxi,gxi,pxi][i])));
Report("Lemma 4.2: c_B = d_xi for these parameters",
  Same(SubsV(cB, [bxi,gxi,pxi]), xi*s + one/2 + t/xi));
ex := List(Mvals, f -> Value(f, [zeta, xx], [2, -2]));;
Report("Example 4.4: zeta=2, [x:y]=[-2:1] gives beta=1, gamma=psi=9/8",
  Same(ex, [1, 9/8, 9/8]));
Report("Example 4.4: Theta = Sigma = 0",
  Same(Value(Subs(ThetaP, ex),[zeta],[2]), 0) and Same(Value(Subs(SigmaP, ex),[zeta],[2]), 0));

#############################################################################
Print("\n--- 15. Lemma 3.25 and Proposition 3.32 ---\n");
#############################################################################
Report("Lemma 3.25: u1,u2,v1,v2 have a1 = 0 and ell = 0",
  ForAll([u1,u2,v1,v2], w -> Same(w[1],0) and Same(ell(w),0)));
Report("Lemma 3.25: d2 has a1 = 0; Phi(g) = 0; k(zeta-1)^2 = 8 zeta",
  Same(d2[1],0) and Same(PhiW(g),0) and Same(k*(zeta-1)^2, 8*zeta));
Report("Prop 3.32: c(bc), c(ac), c r as in [GS, Table 1]",
  Same(M(c,E9(5)), (beta/2)*c + E9(5)/2) and Same(M(c,E9(6)), (gamma/2)*c + E9(6)/2)
  and Same(M(c,E9(9)), (psi/2)*c + E9(9)/2));
Report("Prop 3.32: beta=gamma=psi=0 => B-projections of ac,bc,p,q,r vanish",
  ForAll([5,6,7,8,9], i -> Same(SubsV(E9(i) - ProjW(E9(i)), [0,0,0]), Z9)));

Print("\nALL CHECKS PASSED: ", ForAll(results, x -> x = true), "\n");
