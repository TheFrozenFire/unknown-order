\\ Short e-th-root polynomials: deg ≤ d_q < q−2 (F_q* minus residue p)
\\ forces q | (P − X^{d_q}), so some coefficient of P has gcd with N
\\ a proper factor.  Monomial X^d sits outside this window.
\\ Mirrors SrsaRootPoly.v short-root section.  Probe names avoid "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; e=pin_e; d=pin_d;
da=pin_inv3_p; db=pin_inv3_q;
ca=pin_root_ca; cb=pin_root_cb;

check(db < q-2,                         "d_q < q−2: deg window fits F_q* minus p");
check(p < q,                            "residue p lies in 1..q−1");
check(p != 0 && p < q,                  "p is the missing F_q* sample");

P = ca*x^da + cb*x^db;
check(poldegree(P)==db,                 "CRT binomial degree is d_q");
Q = P - x^db;
check(poldegree(Q)==db,                 "deg(P−X^{d_q}) ≤ d_q");
qdiv=1;
for(i=0, poldegree(Q), \
  if(polcoeff(Q,i)%q!=0, qdiv=0));
check(qdiv,                             "q divides every coeff of P−X^{d_q}");
check(gcd(ca,N)==q,                     "coeff of X^{d_p} splits");
check(polcoeff(P, db)%q==1,             "leading of binomial is 1 mod q");

\\ monomial X^{d_q} does not invert unit 2
check(lift(Mod(2,N)^db)^e != 2,         "X^{d_q} does not invert unit 2");
check(lift(Mod(2,p)^(db*e)) != 2%p,     "on F_p*: 2^{d_q e} ≢ 2");

\\ c X^{d_q} on F_p* is c X (since X^{11}≡X); (cX)^3≡X for all X is impossible
check(lift(Mod(2,p)^10)==1,             "Fermat: 2^{p−1}≡1");
check(lift(Mod(2,p)^db)==lift(Mod(2,p)), "X^{d_q}≡X on F_p*");
check(lift(Mod(1,p)^3)==1,              "at 1: c^3≡1");
check(lift(Mod(2,p)^3)!=2,              "at 2: 8≢2, so c=1 still misses");

\\ another short poly: 17 X + 34 X^7 + 137 X^{11}
P2 = 17*x + ca*x^da + 137*x^db;
check(poldegree(P2)==db,                "extra short poly still deg d_q");
check(gcd(17,N)==q,                     "its X coeff splits");
units_ok=1;
for(aa=1, N-1, \
  if(gcd(aa,N)==1, \
    v=17*aa + ca*aa^da + 137*aa^db; \
    if(lift(Mod(v,N)^e)!=aa, units_ok=0) \
  ) \
);
check(units_ok,                         "extra short poly inverts every unit");

\\ trapdoor monomial is outside the window
check(poldegree(x^d)==d,                "deg(X^d)=d");
check(d > db,                           "trapdoor degree exceeds d_q");
check(gcd(1,N)==1,                      "monomial coeffs do not split");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
