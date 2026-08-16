\\ CAS witnesses — Fermat factoring: close primes make N a near-square.
\\ Mirrors FermatFactor.v: N = ((p+q)/2)^2 - ((p-q)/2)^2.
\\ Classic vector 8051 = 83*97 (one Fermat step from ceil(sqrt(N))).

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

fermat_sum(p, q) = (p + q) \ 2;
fermat_diff(p, q) = (p - q) \ 2;
ceil_sqrt(n) = { s = sqrtint(n); if(s*s == n, s, s+1) };

p = 83; q = 97; N = p*q;
check(N == 8051,                        "N = 83*97 = 8051");
check(fermat_sum(p,q) == 90,            "(p+q)/2 = 90");
check(fermat_diff(p,q) == -7,           "(p-q)/2 = -7");
check(90^2 - N == 7^2,                  "90^2 - N = 7^2  (identity)");
check(N == 90^2 - 7^2,                  "N = s^2 - d^2");
check(ceil_sqrt(N) == 90,               "ceil(sqrt(8051)) = 90");
check(90 + 7 == 97 && 90 - 7 == 83,     "Fermat recovers {83,97} in 0 extra steps");

\\ twins: p and nextprime(p+1) — bit-balanced and still Fermat-food
p2 = 101; q2 = 103; N2 = p2*q2;
s2 = fermat_sum(p2,q2); d2 = fermat_diff(p2,q2);
check(s2*s2 - N2 == d2*d2,              "identity on 101*103");
check(ceil_sqrt(N2) == s2,              "twins: ceil(sqrt(N)) = (p+q)/2");
check(s2 + d2 == p2 && s2 - d2 == q2,   "twins recover in 0 extra steps");

\\ far-apart contrast: same p=83, q=nextprime(400)
p3 = 83; q3 = 401; N3 = p3*q3;
s3 = fermat_sum(p3,q3); d3 = fermat_diff(p3,q3);
check(s3*s3 - N3 == d3*d3,              "identity on 83*401");
check(s3 - ceil_sqrt(N3) > 10,          "far primes: many Fermat steps from ceil(sqrt(N))");
check(s3 + d3 == p3 && s3 - d3 == q3,   "still recovers at the true sum");

\\ unbalanced: small p is the whole secret (trial / ECM bound is p, not N)
p4 = 11; q4 = 10007; N4 = p4*q4;
check(isprime(p4) && isprime(q4),       "11 and 10007 prime");
check(N4 % p4 == 0,                     "p | N");
check(p4^2 < N4,                        "p < sqrt(N): trial bound is p");
g = 1; for(t = 2, p4, if(N4 % t == 0, g = t; break));
check(g == p4,                          "trial division finds the small prime");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
