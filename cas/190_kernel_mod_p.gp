\\ Geometric kernel K ≡ X^{q-2} (mod p) as polynomials: every
\\ lower coefficient is a positive power of p.  Hence K(a) ≡
\\ a^{q-2} (mod p) for every a.
\\ Mirrors SrsaRootPoly.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q;
K=0; for(j=0, q-2, K += p^j * x^(q-2-j));
check(polcoeff(K, q-2)==1,              "leading coeff of K is 1");
low=1;
for(i=0, q-3, if(polcoeff(K,i)%p != 0, low=0));
check(low,                              "lower coeffs of K are 0 mod p");
at2=lift(Mod(subst(K,x,2),p));
check(at2==lift(Mod(2,p)^(q-2)),        "K(2)≡2^{q-2} (mod p)");
at5=lift(Mod(subst(K,x,5),p));
check(at5==lift(Mod(5,p)^(q-2)),        "K(5)≡5^{q-2} (mod p)");

K1363=0; for(j=0, pin1363_q-2, K1363 += pin1363_p^j * x^(pin1363_q-2-j));
low2=1;
for(i=0, pin1363_q-3, if(polcoeff(K1363,i)%pin1363_p != 0, low2=0));
check(low2,                             "1363 lower coeffs 0 mod p");
check(polcoeff(K1363, pin1363_q-2)==1,  "1363 K is monic");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
