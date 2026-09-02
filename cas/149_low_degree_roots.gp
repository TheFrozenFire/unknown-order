\\ Low-degree + vanish on 1..10 ⇒ 11 divides every coefficient.
\\ 1..10 are units of Z/187Z and all of F_11*.  Bound is strict:
\\ X^{10}−1 vanishes on F_11* at deg = p−1.  Vanishing on (Z/NZ)*
\\ does not sample 11 mod 17, so this is not a 17-divides claim.
\\ Mirrors ZPoly poly_prime_roots_divides / SrsaResidualGRA.v.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p=11; q=17; N=p*q;

units10 = 1;
for(a=1, 10, \
  if(gcd(a,N)!=1, units10=0));
check(units10,                              "1..10 are units of Z/NZ");
check(#vector(10,k,k)==10,                  "ten residues 1..10");

distinct=1;
for(a=1, 10, \
  for(b=a+1, 10, \
    if((b-a)%p==0, distinct=0)));
check(distinct,                             "1..10 pairwise distinct mod 11");

\\ a poly with 11 | every coeff vanishes on F_11 and has deg < 10
Q = 11*(x^2 + 3*x + 5);
check(poldegree(Q)==2,                      "deg(11(X^2+3X+5))=2");
check(2 < p-1,                              "2 < p−1=10");
vanQ=1;
for(a=1, 10, \
  if(lift(Mod(subst(Q,x,a),p))!=0, vanQ=0));
check(vanQ,                                 "11(X^2+3X+5) vanishes on 1..10");
check(polcoeff(Q,0)%p==0,                   "const coeff 0 mod 11");
check(polcoeff(Q,1)%p==0,                   "linear coeff 0 mod 11");
check(polcoeff(Q,2)%p==0,                   "quadratic coeff 0 mod 11");

\\ identity X^3−X is low-degree but linear −1 is not 0 mod 11
Q3 = x^3 - x;
check(poldegree(Q3)==3 && 3 < p-1,          "X^3−X is low-degree");
check(polcoeff(Q3,1)%p!=0,                  "linear −1 is not 0 mod 11");
check(lift(Mod(subst(Q3,x,2),p))!=0,        "so unit 2 is not a root");

\\ a deg-3 poly with a coeff not 0 mod 11 misses a unit
R = x^3 + x + 1;
miss=0;
for(a=1, 10, \
  if(lift(Mod(subst(R,x,a),p))!=0, miss=1));
check(miss,                                 "X^3+X+1 misses a unit of F_11");
check(polcoeff(R,0)%p!=0,                   "const 1 is not 0 mod 11");

\\ boundary: Fermat X^{10}−1 vanishes on F_11* but deg is not < p−1
F = x^10 - 1;
check(poldegree(F)==10,                     "deg(X^{10}−1)=10 = p−1, not strictly below");
vanF=1;
for(a=1, 10, \
  if(lift(Mod(subst(F,x,a),p))!=0, vanF=0));
check(vanF,                                 "X^{10}−1 vanishes on F_11* (Fermat)");
check(polcoeff(F,0)%p!=0,                   "const −1 not 0 mod 11: the bound is strict");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
