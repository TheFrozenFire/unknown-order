\\ The short e-th-root window is sharp: deg < d_q cannot invert
\\ every unit (P−X^{d_q} has leading −1, q does not divide −1).
\\ A nodiv GRA whose degree bound is ≤ d_q and that inverts every
\\ unit denotes a short root poly, hence a coeff splits N.
\\ Mirrors SrsaRootPoly.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; e=pin_e;
da=pin_inv3_p; db=pin_inv3_q;
ca=pin_root_ca; cb=pin_root_cb;

check(db < q-2,                         "d_q < q−2");
check((-1)%q != 0,                      "q does not divide leading −1 of P−X^{d_q}");
check(gcd(1,q)==1,                      "hence q does not divide −1");

\\ deg 7 = d_p < d_q: X^{d_p} does not invert unit 2
check(poldegree(x^da)==da,              "deg(X^{d_p})=d_p < d_q");
check(da < db,                          "d_p < d_q");
check(lift(Mod(2,N)^da)^e != 2,         "X^{d_p} does not invert unit 2");

\\ identity (deg 1) and square (deg 2) miss leftover invert
check(lift(Mod(pin_y,N)^e) != pin_y,    "identity tape y^e ≢ y");
check(lift(Mod(pin_y,N)^2)^e != pin_y,  "square tape (y^2)^e ≢ y");

\\ at the bound, CRT binomial inverts and splits
P = ca*x^da + cb*x^db;
check(poldegree(P)==db,                 "CRT binomial sits at deg = d_q");
check(gcd(ca,N)==q,                     "and a coefficient splits");
units_ok=1;
for(aa=1, N-1, \
  if(gcd(aa,N)==1, \
    v=ca*aa^da + cb*aa^db; \
    if(lift(Mod(v,N)^e)!=aa, units_ok=0) \
  ) \
);
check(units_ok,                         "binomial inverts every unit at deg = d_q");

\\ nodiv GRA degree bounds: identity 1, square 2, cube 3, all < d_q
check(1 < db && 2 < db && 3 < db,      "low-degree nodiv tapes sit strictly below d_q");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
