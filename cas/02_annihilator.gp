\\ CAS witnesses — M = ed−1 annihilates (Z/NZ)*.
\\ Mirrors annihilates_units / rsa_test_annihilator / carmichael_semiprime.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 11; q = 17; N = p*q; e = 3; d = 27;
lam = lcm(p-1, q-1);
M = e*d - 1;
check(M == 80,                          "ed−1 = 80 = λ");
check(M % lam == 0,                     "λ | ed−1");

\\ every unit satisfies a^M ≡ 1 (mod N)
ann_fail = 0; n_units = 0;
for(a = 1, N-1, \
  if(gcd(a,N)==1, \
    n_units++; \
    if(lift(Mod(a,N)^M) != 1, ann_fail++) \
  ) \
);
check(n_units == eulerphi(N),           "counted φ(N) units");
check(ann_fail == 0,                    "a^{ed−1} ≡ 1 for every unit (exhaustive)");

\\ Euler: a^φ ≡ 1
eu_fail = 0;
for(a = 1, N-1, \
  if(gcd(a,N)==1 && lift(Mod(a,N)^eulerphi(N)) != 1, eu_fail++) \
);
check(eu_fail == 0,                     "a^φ ≡ 1 for every unit (exhaustive)");

\\ a second instance (e=5, p=5, q=13): λ=12, d=5, M=24
p2 = 5; q2 = 13; N2 = p2*q2; e2 = 5; d2 = 5;
lam2 = lcm(p2-1, q2-1);
M2 = e2*d2 - 1;
check(lam2 == 12,                       "second instance λ(65) = 12");
check(M2 % lam2 == 0,                   "24 is a multiple of 12");
ann2 = 0;
for(a = 1, N2-1, \
  if(gcd(a,N2)==1 && lift(Mod(a,N2)^M2) != 1, ann2++) \
);
check(ann2 == 0,                        "annihilator on N=65, e=d=5");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
