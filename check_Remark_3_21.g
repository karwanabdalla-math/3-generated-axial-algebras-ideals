#############################################################################
##  check_Remark_3_21.g
##  Symbolic verification of Remark 3.21 in the paper on ideals in
##  3-generated primitive axial algebras of Jordan type 1/2.
##
##  Assume Theta = alpha + beta + gamma - 2 psi - 1 = 0, where
##  alpha = (zeta+1)^2/(4 zeta), and consider (Proposition 3.20)
##     Q(x,y) = 2((x+y)^2 - zeta^2 y^2) beta - 2 zeta x(x+2y) gamma
##              - x(zeta-1) h,          h = y(zeta-1) - x.
##  We check:
##    1. Q is a binary quadratic form A2 x^2 + A1 xy + A0 y^2;
##    2. its discriminant is -64 zeta^2 Sigma = (8 zeta)^2 (psi^2 - alpha beta gamma),
##       where Sigma = alpha beta gamma - psi^2;
##    3. Q is never identically zero when zeta <> +-1.
##  Hence the number of roots [x:y] of Q in P^1(F) is 2, 0 or 1 according
##  as psi^2 - alpha beta gamma is a nonzero square, a non-square, or 0.
##  Finally, we check every number in the Example after Remark 3.21
##  (zeta = 3, beta = 1/5, psi = 1/7 over Q).
#############################################################################

zeta  := Indeterminate(Rationals, "zeta");;
beta  := Indeterminate(Rationals, "beta");;
psi   := Indeterminate(Rationals, "psi");;
x     := Indeterminate(Rationals, "x");;
y     := Indeterminate(Rationals, "y");;
alpha := (zeta+1)^2/(4*zeta);;
gamma := 1 - alpha - beta + 2*psi;;          # the condition Theta = 0
SigmaP := alpha*beta*gamma - psi^2;;

Same := function(u, v) return IsZero(u - v); end;;
results := [];;
Report := function(name, ok)
  Add(results, ok);
  Print(String(name, -66), " ", ok, "\n");
end;;

h  := y*(zeta-1) - x;;
Q  := 2*((x+y)^2 - zeta^2*y^2)*beta - 2*zeta*x*(x+2*y)*gamma - x*(zeta-1)*h;;
A2 := Value(Q, [x,y], [1,0]);;
A0 := Value(Q, [x,y], [0,1]);;
A1 := Value(Q, [x,y], [1,1]) - A2 - A0;;

Report("1. Q = A2 x^2 + A1 xy + A0 y^2",
  Same(Q, A2*x^2 + A1*x*y + A0*y^2));
Report("2. discriminant A1^2 - 4 A2 A0 = (8 zeta)^2 (psi^2 - alpha beta gamma)",
  Same(A1^2 - 4*A2*A0, (8*zeta)^2*(psi^2 - alpha*beta*gamma)));
Report("   equivalently, discriminant = -64 zeta^2 Sigma",
  Same(A1^2 - 4*A2*A0, -64*zeta^2*SigmaP));
Report("3. A0 = 2 beta (1 - zeta^2)",
  Same(A0, 2*beta*(1-zeta^2)));
Report("   at beta = 0:  A1 - 2 A2 = -(zeta^2 - 1)",
  Same(Value(A1 - 2*A2, [beta], [0]), -(zeta^2-1)));
Print("   (so if A0 = A1 = A2 = 0 then beta = 0 and zeta^2 = 1, impossible)\n");

## An example over Q: zeta = 3, beta = 1/5, psi = 1/7 (so Theta = 0).
## Then psi^2 - alpha beta gamma = 953/11025 is not a square in Q, so Q has
## no root in P^1(Q): the two ideals D0 + M_[x:y] exist only over Q(sqrt 953).
d := Value(psi^2 - alpha*beta*gamma, [zeta,beta,psi], [3,1/5,1/7]);;
Report("example zeta=3, beta=1/5, psi=1/7: psi^2 - alpha beta gamma = 953/11025",
  d = 953/11025);

Report("example: alpha = 4/3 and gamma = 1 - alpha - beta + 2 psi = -26/105",
  Value(alpha,[zeta],[3]) = 4/3 and Value(gamma,[zeta,beta,psi],[3,1/5,1/7]) = -26/105);
Report("example: 953 is not a square (953 is prime)",
  RootInt(953)^2 <> 953 and IsPrimeInt(953));
## The roots of Q in the example (Example after Remark 3.21):
## Q(x,1) is a nonzero multiple of 17 x^2 - x - 14, whose roots are
## (1 +- sqrt(953))/34, and Q(1,0) <> 0, so [1:0] is not a root.
vals := [3, 1/5, 1/7];;
Qex  := Value(Q,  [zeta,beta,psi,y], Concatenation(vals,[1]));;
A2ex := Value(A2, [zeta,beta,psi], vals);;
Report("example: Q(x,1) is a nonzero multiple of 17 x^2 - x - 14",
  A2ex <> 0 and Same(17*Qex/A2ex, 17*x^2 - x - 14));
Report("example: discriminant of 17 x^2 - x - 14 is 953",
  (-1)^2 - 4*17*(-14) = 953);
Report("example: (1 +- sqrt 953)/34 are the roots of 17 x^2 - x - 14",
  ForAll([1,-1], e -> 17*((1+e*Sqrt(953))/34)^2 - (1+e*Sqrt(953))/34 - 14 = 0));

Print("\nALL CHECKS PASSED: ", ForAll(results, r -> r = true), "\n");
