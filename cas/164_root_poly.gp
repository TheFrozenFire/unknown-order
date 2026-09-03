\\ Two writings of an e-th root polynomial on units.
\\ CRT binomial c_p X^{d_p} + c_q X^{d_q} has coefficients whose
\\ gcd with N is a factor.  Monomial X^d agrees as a function on
\\ units, coefficients do not split, and (e,d) is the trapdoor
\\ (Miller).  Not residual-solver ⇒ factor: the TM wrote p,q into
\\ the coefficients (or d into the degree).
\\ Mirrors SrsaRootPoly.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; e=pin_e; d=pin_d; lam=pin_lam;
y=pin_y; xx=pin_x;
da=pin_inv3_p; db=pin_inv3_q;
ca=q*lift(1/Mod(q,p));
cb=p*lift(1/Mod(p,q));

check(ca == pin_root_ca,                "pin_root_ca = q·q^{-1} mod p");
check(cb == pin_root_cb,                "pin_root_cb = p·p^{-1} mod q");
check(ca%p==1 && ca%q==0,               "c_a ≡ 1 (mod p), 0 (mod q)");
check(cb%p==0 && cb%q==1,               "c_b ≡ 0 (mod p), 1 (mod q)");
check(gcd(ca,N)==q,                     "gcd(c_a,N)=q");
check(gcd(cb,N)==p,                     "gcd(c_b,N)=p");
check((e*da)%(p-1)==1,                  "e·d_p ≡ 1 (mod p-1)");
check((e*db)%(q-1)==1,                  "e·d_q ≡ 1 (mod q-1)");
check((e*d)%lam==1,                     "e·d ≡ 1 (mod λ)");
check(da!=db,                           "local inverses differ");

Py = ca*y^da + cb*y^db;
check(lift(Mod(Py,N))==xx,              "binomial at y is leftover x");
check(lift(Mod(Py,N)^e)==y,             "binomial cubes to y");
check(lift(Mod(y,N)^d)==xx,             "monomial X^d at y is leftover x");

\\ both invert every unit, and they agree as functions
units_ok = 1; agree_ok = 1; miss = 0;
for(aa = 1, N-1, \
  if(gcd(aa,N)==1, \
    Pv = ca*aa^da + cb*aa^db; \
    if(lift(Mod(Pv,N)^e)!=aa, units_ok=0; miss=aa); \
    if(lift(Mod(Pv,N))!=lift(Mod(aa,N)^d), agree_ok=0) \
  ) \
);
check(units_ok==1,                      "binomial^e ≡ id on every unit");
check(agree_ok==1,                      "binomial agrees with X^d on units");

check(poldegree(ca*x^da + cb*x^db)==db, "binomial degree is d_q");
check(poldegree(x^d)==d,                "monomial degree is d");
check(polcoeff(ca*x^da + cb*x^db, da)==ca, "coeff of X^{d_p} is c_a");
check(polcoeff(ca*x^da + cb*x^db, db)==cb, "coeff of X^{d_q} is c_b");
check(polcoeff(x^d, d)==1,              "monomial leading coeff 1");
check(gcd(1,N)==1,                      "monomial coeffs do not split N");
check(3*db >= p-1,                      "binomial escapes the low-degree window");
check(d >= p-1,                         "monomial X^d is not low-degree");
check(ca*x^da + cb*x^db != x^d,         "binomial ≠ monomial as polynomials");

\\ a second unit, not the pin challenge
check(gcd(2,N)==1,                      "2 is a unit");
P2 = ca*2^da + cb*2^db;
check(lift(Mod(P2,N)^e)==2,             "binomial inverts unit 2");
check(lift(Mod(2,N)^d)==lift(Mod(P2,N)), "X^d inverts unit 2 the same way");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
