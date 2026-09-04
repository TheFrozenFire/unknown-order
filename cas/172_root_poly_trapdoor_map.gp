\\ Any polynomial that inverts every unit agrees with X^d on (Z/NZ)*.
\\ Unique unit e-th root; the map is the trapdoor map, not a new
\\ solver.  CRT binomial, monomial X^d, and an extra short poly all
\\ agree as functions.  Mirrors SrsaRootPoly.v.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; e=pin_e; d=pin_d;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;
g=pin_g;

Pbin = ca*x^da + cb*x^db;
Pmon = x^d;
Pshort = 17*x + ca*x^da + 137*x^db;

agree=1; agreem=1; agrees=1;
for(aa=1, N-1, \
  if(gcd(aa,N)==1, \
    td=lift(Mod(aa,N)^d); \
    vb=lift(Mod(subst(Pbin,x,aa),N)); \
    vm=lift(Mod(subst(Pmon,x,aa),N)); \
    vs=lift(Mod(subst(Pshort,x,aa),N)); \
    if(vb!=td, agree=0); \
    if(vm!=td, agreem=0); \
    if(vs!=td, agrees=0) \
  ) \
);
check(agree,                            "binomial agrees with X^d on units");
check(agreem,                           "monomial X^d agrees with y^d on units");
check(agrees,                           "extra short poly agrees with X^d on units");

check(lift(Mod(subst(Pbin,x,g),N))==lift(Mod(g,N)^d), "binomial at g is g^d");
check(lift((Mod(g,N)^d)^e)==g,          "g^d is the e-th root of g");
check(poldegree(Pbin)!=poldegree(Pmon), "binomial ≠ monomial as polynomials");
check(gcd(ca,N)==q,                     "binomial still splits via a coeff");
check(gcd(1,N)==1,                      "monomial leading coeff does not split");

\\ same function identity on the 1363 frozen pin
N2=pin1363_N; e2=pin1363_e; d2=pin1363_d;
da2=pin1363_inv3_p; db2=pin1363_inv3_q;
ca2=pin1363_root_ca; cb2=pin1363_root_cb;
P2=ca2*x^da2 + cb2*x^db2;
agree2=1;
for(aa=1, N2-1, \
  if(gcd(aa,N2)==1, \
    if(lift(Mod(subst(P2,x,aa),N2))!=lift(Mod(aa,N2)^d2), agree2=0) \
  ) \
);
check(agree2,                           "1363 binomial agrees with X^d on units");
check((e2*d2)%pin1363_lam==1,           "1363 e·d ≡ 1 (mod λ)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
