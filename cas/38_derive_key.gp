\\ CAS — toy derive_key from a seed: emit (p,q,e,d) discharging the numeric spec.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

\\ Seeded classes (per-key aux).  Toy bits, not regime_1024.
\\ p-slot: (3,5,7,13,19) a=13099; q-slot: (5,3,7,13,19) a=21611
ap = 13099; aq = 21611; M = 103740;
p = ap; q = aq;
check(isprime(p) && isprime(q),          "both candidates prime");
check(p != q,                            "distinct");
check(p <= q && q <= 2*p,                "balanced");
check(abs(q-p) >= 2^13,                  "far at gap=13");
e = 65537;
lam = lcm(p-1, q-1);
check(gcd(e, lam) == 1,                  "e coprime to λ");
d = lift(1/Mod(e, lam));
check((e*d) % lam == 1 && d > 0,         "d ≡ e^{-1} (mod λ)");
N = p*q;
check(!(18*d*d*d < N),                   "d is not Wiener-small");
check(e >= 65537,                        "e not tiny");
check(p%4==3 && q%4==3,                  "both Blum");
check((p-1)%3==0 && (p+1)%5==0,          "p-slot rulers");
check((q-1)%5==0 && (q+1)%3==0,          "q-slot rulers");

\\ determinism: same numbers from the same named seed material
seed = 1;
check(ap == 13099 && aq == 21611,        "same seed material, same pair");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
