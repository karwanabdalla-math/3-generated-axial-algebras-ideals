#############################################################################
##  check_Table1_vs_BG.g
##
##  Independent check of Table 1 of the paper (the multiplication table of
##  the universal algebra A(alpha,beta,gamma,psi) of [GS, Table 1]) and of
##  the Gram matrix [GS, Table 5] against the public Mathematica notebook
##  "3gen axial algebra.nb" of Bildanov and Gorshkov,
##     https://github.com/RavilBildanov/3gen-axial-algebras
##  (commit 3fb4481, December 2023).
##
##  Their notebook does not store the table: it fills in the first three
##  rows (products with a, b, c) by hand, symmetrizes, and then computes the
##  remaining products in three rounds from the fusion law, each round using
##  the product defined by the table as it stood after the previous round.
##  Below this construction is transcribed line by line (their eta = 1/2,
##  phi = psi, abc = a(bc) = p, bac = b(ac) = q, cab = c(ab) = r), and the
##  result is compared with our table, symbolically in the four parameters.
##
##  Basis order (the same in both):
##    1:a  2:b  3:c  4:ab  5:bc  6:ac  7:p=a(bc)  8:q=b(ac)  9:r=c(ab)
#############################################################################

alpha := Indeterminate(Rationals, "alpha");;
beta  := Indeterminate(Rationals, "beta");;
gamma := Indeterminate(Rationals, "gamma");;
psi   := Indeterminate(Rationals, "psi");;
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

results := [];;
Report := function(name, ok)
  Add(results, ok);
  Print(String(name, -66), " ", ok, "\n");
end;;

#############################################################################
##  The construction of Bildanov and Gorshkov
#############################################################################
alp := alpha;; bet := beta;; gam := gamma;; phi := psi;; eta := 1/2;;
z := Zero(alpha);; o := One(alpha);;
U := function(i) local v; v := List([1..9], k -> z); v[i] := o; return v; end;;
a := U(1);; b := U(2);; c := U(3);; ab := U(4);; bc := U(5);; ac := U(6);;
abc := U(7);; bac := U(8);; cab := U(9);;

mas := List([1..9], i -> List([1..9], j -> List([1..9], k -> z)));;
mas[1] := o*[[1,0,0,0,0,0,0,0,0],[0,0,0,1,0,0,0,0,0],[0,0,0,0,0,1,0,0,0],
  [alp-eta*alp,0,0,eta,0,0,0,0,0],[0,0,0,0,0,0,1,0,0],
  [gam-eta*gam,0,0,0,0,eta,0,0,0],[phi*(1-eta),0,0,0,0,0,eta,0,0],
  [alp*gam+1/2*eta*phi-2*eta*alp*gam,0,0,1/2*eta*gam,0,1/2*eta*alp,1/2*eta,1/2*eta,-1/2*eta],
  [alp*gam+1/2*eta*phi-2*eta*alp*gam,0,0,1/2*eta*gam,0,1/2*eta*alp,1/2*eta,-1/2*eta,1/2*eta]];;
mas[2] := o*[[0,0,0,1,0,0,0,0,0],[0,1,0,0,0,0,0,0,0],[0,0,0,0,1,0,0,0,0],
  [0,alp-eta*alp,0,eta,0,0,0,0,0],[0,bet-eta*bet,0,0,eta,0,0,0,0],
  [0,0,0,0,0,0,0,1,0],
  [0,alp*bet+1/2*eta*phi-2*eta*alp*bet,0,1/2*eta*bet,1/2*eta*alp,0,1/2*eta,1/2*eta,-1/2*eta],
  [0,phi*(1-eta),0,0,0,0,0,eta,0],
  [0,alp*bet+1/2*eta*phi-2*eta*alp*bet,0,1/2*eta*bet,1/2*eta*alp,0,-1/2*eta,1/2*eta,1/2*eta]];;
mas[3] := o*[[0,0,0,0,0,1,0,0,0],[0,0,0,0,1,0,0,0,0],[0,0,1,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,1],[0,0,bet-eta*bet,0,eta,0,0,0,0],
  [0,0,gam-eta*gam,0,0,eta,0,0,0],
  [0,0,bet*gam+1/2*eta*phi-2*eta*bet*gam,0,1/2*eta*gam,1/2*eta*bet,1/2*eta,-1/2*eta,1/2*eta],
  [0,0,bet*gam+1/2*eta*phi-2*eta*bet*gam,0,1/2*eta*gam,1/2*eta*bet,-1/2*eta,1/2*eta,1/2*eta],
  [0,0,phi*(1-eta),0,0,0,0,0,eta]];;
for i in [1..9] do for j in [1..9] do mas[j][i] := mas[i][j]; od; od;

## prod uses a frozen copy of mas, as Mathematica's prod[u_,v_]=... does.
Snap := function()
  local S;
  S := StructuralCopy(mas);
  return function(u, v)
    local w, i, j;
    w := List([1..9], k -> z);
    for i in [1..9] do for j in [1..9] do
      if not IsZero(u[i]) and not IsZero(v[j]) then
        w := w + u[i]*v[j]*S[i][j];
      fi;
    od; od;
    return w;
  end;
end;;

prod := Snap();;
mas[4][4] := prod(a,prod(b,ab-eta*b))+eta*prod(b,ab);
mas[4][5] := prod(b,prod(a,bc-eta*c))+eta*cab;
mas[4][6] := prod(a,prod(b,ac-eta*c))+eta*cab;
mas[6][4] := mas[4][6];  mas[5][4] := mas[4][5];
mas[5][5] := prod(b,prod(c,bc-eta*c))+eta*prod(c,bc);
mas[5][6] := prod(c,prod(b,ac-eta*a))+eta*abc;
mas[6][5] := mas[5][6];
mas[6][6] := prod(a,prod(c,ac-eta*c))+eta*prod(c,ac);

prod := Snap();;
mas[4][7] := prod(a,prod(b,abc-eta*bc))+eta*prod(ab,bc);
mas[4][8] := prod(b,prod(a,bac-eta*ac))+eta*prod(ab,ac);
mas[4][9] := -mas[4][8]+prod(a,prod(b,cab+bac-eta*bc-eta*gam*b-eta*alp*c))
             +prod(ab,eta*bc+eta*gam*b+eta*alp*c);
mas[7][4] := mas[4][7];  mas[8][4] := mas[4][8];  mas[9][4] := mas[4][9];
mas[5][8] := prod(b,prod(c,bac-eta*ac))+eta*prod(bc,ac);
mas[5][9] := prod(c,prod(b,cab-eta*ab))+eta*prod(bc,ab);
mas[5][7] := -mas[5][9]+prod(b,prod(c,abc+cab-eta*ac-eta*bet*a-eta*alp*c))
             +prod(bc,eta*ac+eta*bet*a+eta*alp*c);
mas[7][5] := mas[5][7];  mas[8][5] := mas[5][8];  mas[9][5] := mas[5][9];
mas[6][7] := prod(a,prod(c,abc-eta*bc))+eta*prod(ac,bc);
mas[6][9] := prod(c,prod(a,cab-eta*ab))+eta*prod(ac,ab);
mas[6][8] := -mas[6][9]+prod(a,prod(c,bac+cab-eta*bc-eta*gam*b-eta*alp*c))
             +prod(ac,eta*bc+eta*gam*b+eta*alp*c);
mas[7][6] := mas[6][7];  mas[8][6] := mas[6][8];  mas[9][6] := mas[6][9];

prod := Snap();;
mas[7][7] := prod(a,prod(bc,abc-eta*bc))+eta*prod(bc,abc);
mas[8][8] := prod(b,prod(ac,bac-eta*ac))+eta*prod(ac,bac);
mas[9][9] := prod(c,prod(ab,cab-eta*ab))+eta*prod(ab,cab);
xyxz := prod(a,prod(bc,bac+cab-eta*bc-eta*gam*b-eta*alp*c))+prod(eta*bc+eta*gam*b+eta*alp*c,abc);;
yxyz := prod(b,prod(ac,abc+cab-eta*ac-eta*bet*a-eta*alp*c))+prod(eta*ac+eta*bet*a+eta*alp*c,bac);;
zxzy := prod(c,prod(ab,abc+bac-eta*ab-eta*bet*a-eta*gam*b))+prod(eta*ab+eta*bet*a+eta*gam*b,cab);;
mas[7][8] := 1/2*(xyxz+yxyz-zxzy);
mas[7][9] := 1/2*(xyxz+zxzy-yxyz);
mas[8][9] := 1/2*(yxyz+zxzy-xyxz);
mas[8][7] := mas[7][8];  mas[9][7] := mas[7][9];  mas[9][8] := mas[8][9];

## Their Gram matrix, copied from the notebook (section "Gram matrix for
## standard basis").
BGG := o*[[1,alpha,gamma,alpha,psi,gamma,psi,1/2*alpha*gamma+1/2*psi,1/2*alpha*gamma+1/2*psi],[alpha,1,beta,alpha,beta,psi,1/2*alpha*beta+1/2*psi,psi,1/2*alpha*beta+1/2*psi],[gamma,beta,1,psi,beta,gamma,1/2*beta*gamma+1/2*psi,1/2*beta*gamma+1/2*psi,psi],[alpha,alpha,psi,1/2*alpha^2+1/2*alpha,1/2*alpha*beta+1/2*psi,1/2*alpha*gamma+1/2*psi,1/4*alpha*beta+1/2*alpha*psi+1/4*psi,1/4*alpha*gamma+1/2*alpha*psi+1/4*psi,1/4*alpha*beta+1/4*alpha*gamma+1/2*alpha*psi],[psi,beta,beta,1/2*alpha*beta+1/2*psi,1/2*beta^2+1/2*beta,1/2*beta*gamma+1/2*psi,1/4*alpha*beta+1/4*beta*gamma+1/2*beta*psi,1/4*beta*gamma+1/2*beta*psi+1/4*psi,1/4*alpha*beta+1/2*beta*psi+1/4*psi],[gamma,psi,gamma,1/2*alpha*gamma+1/2*psi,1/2*beta*gamma+1/2*psi,1/2*gamma^2+1/2*gamma,1/4*beta*gamma+1/2*gamma*psi+1/4*psi,1/4*alpha*gamma+1/4*beta*gamma+1/2*gamma*psi,1/4*alpha*gamma+1/2*gamma*psi+1/4*psi],[psi,1/2*alpha*beta+1/2*psi,1/2*beta*gamma+1/2*psi,1/4*alpha*beta+1/2*alpha*psi+1/4*psi,1/4*alpha*beta+1/4*beta*gamma+1/2*beta*psi,1/4*beta*gamma+1/2*gamma*psi+1/4*psi,1/8*alpha*beta+1/8*beta*gamma+1/4*beta*psi+1/2*psi^2,1/4*alpha*beta*gamma+1/8*alpha*psi+1/8*beta*gamma+1/8*beta*psi+1/8*gamma*psi+1/4*psi^2,1/4*alpha*beta*gamma+1/8*alpha*beta+1/8*alpha*psi+1/8*beta*psi+1/8*gamma*psi+1/4*psi^2],[1/2*alpha*gamma+1/2*psi,psi,1/2*beta*gamma+1/2*psi,1/4*alpha*gamma+1/2*alpha*psi+1/4*psi,1/4*beta*gamma+1/2*beta*psi+1/4*psi,1/4*alpha*gamma+1/4*beta*gamma+1/2*gamma*psi,1/4*alpha*beta*gamma+1/8*alpha*psi+1/8*beta*gamma+1/8*beta*psi+1/8*gamma*psi+1/4*psi^2,1/8*alpha*gamma+1/8*beta*gamma+1/4*gamma*psi+1/2*psi^2,1/4*alpha*beta*gamma+1/8*alpha*gamma+1/8*alpha*psi+1/8*beta*psi+1/8*gamma*psi+1/4*psi^2],[1/2*alpha*gamma+1/2*psi,1/2*alpha*beta+1/2*psi,psi,1/4*alpha*beta+1/4*alpha*gamma+1/2*alpha*psi,1/4*alpha*beta+1/2*beta*psi+1/4*psi,1/4*alpha*gamma+1/2*gamma*psi+1/4*psi,1/4*alpha*beta*gamma+1/8*alpha*beta+1/8*alpha*psi+1/8*beta*psi+1/8*gamma*psi+1/4*psi^2,1/4*alpha*beta*gamma+1/8*alpha*gamma+1/8*alpha*psi+1/8*beta*psi+1/8*gamma*psi+1/4*psi^2,1/8*alpha*beta+1/8*alpha*gamma+1/4*alpha*psi+1/2*psi^2]];;

## Our Gram matrix [GS, Table 5], as in check_main.g.
al := alpha;; be := beta;; ga := gamma;; ps := psi;;
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

#############################################################################
Print("\n--- Comparison with the notebook of Bildanov and Gorshkov ---\n");
Report("all 81 products e_i e_j agree with Table 1",
  ForAll(Cartesian([1..9],[1..9]), ij -> IsZero(T[ij[1]][ij[2]] - mas[ij[1]][ij[2]])));
Report("all 81 entries of the Gram matrix agree with [GS, Table 5]",
  ForAll(Cartesian([1..9],[1..9]), ij -> IsZero(G[ij[1]][ij[2]] - BGG[ij[1]][ij[2]])));

Print("\nALL CHECKS PASSED: ", ForAll(results, x -> x = true), "\n");
