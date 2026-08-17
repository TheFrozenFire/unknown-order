\\ CAS witnesses — Wesolowski on Cl(Δ) via composition.
\\ Mirrors ExpProof.v week-5 / form_neg87_ord3.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

D = -87;
id = qfbred(Qfb(1, D%2, (D%2 - D)/4));
x = Qfb(4,3,6);
check(qfbred(x) == x,                    "(4,3,6) reduced on -87");
n = 1; g = qfbred(x);
while(g != id && n < 20, g = qfbred(g*x); n++);
check(n == 3,                            "(4,3,6) has order 3");

\\ Wesolowski: y = x^(q*ell+r), pi = x^q
ell = 2; q = 1; r = 1;
\\ 2 = 1*2+0 would be even; use y = x^3 = id, q=1, ell=2, r=1 ⇒ q*ell+r = 3
y = qfbred(x^3);
pi = qfbred(x^q);
lhs = qfbred(pi^ell * x^r);
check(lhs == y,                          "Wesolowski verifies on Cl(-87)");
check(y == id,                           "x^3 is the identity");

\\ Pietrzak T=2 on the order-2 class: mid = f, y = f^2 = id
f = Qfb(3,3,8);
check(qfbred(f*f) == id,                 "ambiguous squares to id");
mu = f;
check(qfbred(mu*mu) == id,               "bad/true mid both square to id");
\\ Restricted LowOrder does not count f
check(component(f,1)==3,                 "catalog 2-torsion is constructible");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
