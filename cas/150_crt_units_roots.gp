\\ CRT lift: vanish on (Z/NZ)* + deg < 10 ⇒ N divides every coefficient.
\\ Residue 11 mod 17 is not a unit of Z/NZ; chinese(Mod(1,11), Mod(11,17))
\\ lifts it to a unit.  Then deg < 10 < 16 forces 17 | coeffs, hence N.
\\ Identity linear −1 is not 0 mod N.  Mirrors SrsaResidualGRA.v.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N;

y11 = lift(chinese(Mod(1,p), Mod(11,q)));
check(y11 % p == 1,                         "CRT lift ≡ 1 (mod 11)");
check(y11 % q == 11,                        "CRT lift ≡ 11 (mod 17)");
check(gcd(y11, N)==1,                       "CRT lift is a unit of Z/NZ");
check(y11 == 45,                            "pin CRT lift of 11 is 45");

units16=1;
for(a=1, 16, \
  if(a!=11 && gcd(a,N)!=1, units16=0));
check(units16,                              "1..16 except 11 are units of Z/NZ");
check(gcd(11,N)==11,                        "11 is not a unit of Z/NZ");

distinct=1;
for(a=1, 16, \
  for(b=a+1, 16, \
    if((b-a)%q==0, distinct=0)));
check(distinct,                             "1..16 pairwise distinct mod 17");
check(10 < 16,                              "deg < 10 is strictly below |F_17*|");

\\ a poly with N | every coeff vanishes on all units
Q = N*(x^2 + 3*x + 5);
check(poldegree(Q)==2 && 2 < 10,            "deg(N(X^2+3X+5))=2 < 10");
vanU=1;
for(a=1, N-1, \
  if(gcd(a,N)==1 && lift(Mod(subst(Q,x,a),N))!=0, vanU=0));
check(vanU,                                 "N(X^2+3X+5) vanishes on all units of Z/NZ");
check(lift(Mod(subst(Q,x,y11),N))==0,       "hence vanishes at the CRT lift of 11");
check(lift(Mod(subst(Q,x,11),q))==0,        "hence vanishes at 11 mod 17");
check(polcoeff(Q,0)%N==0,                   "const coeff 0 mod N");
check(polcoeff(Q,1)%N==0,                   "linear coeff 0 mod N");
check(polcoeff(Q,2)%N==0,                   "quadratic coeff 0 mod N");

\\ 11(X^2+1) is 0 mod 11 on F_11* but not 0 mod 17
S = 11*(x^2 + 1);
check(polcoeff(S,2)%q != 0,                 "11(X^2+1) leading is not 0 mod 17");
miss17=0;
for(a=1, 16, \
  if(lift(Mod(subst(S,x,a),q))!=0, miss17=1));
check(miss17,                               "11(X^2+1) misses a residue of F_17*");

\\ identity linear −1 is not 0 mod N
check((-1)%N != 0,                          "N does not divide −1");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
