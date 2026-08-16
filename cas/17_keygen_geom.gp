\\ CAS witnesses — Type A geometries modern keygens commit.
\\ Mirrors KeyGenGeom.v: shared high bits, increment window, adjacent odds.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

fermat_diff(p, q) = (p - q) \ 2;
ceil_sqrt(n) = { s = sqrtint(n); if(s*s==n, s, s+1) };
fermat_steps(p, q) = (p+q)\2 - ceil_sqrt(p*q);

\\ adjacent odds
p = 101; q = 103;
check(p%2==1 && q%2==1 && abs(p-q)==2,  "101,103 adjacent odds");
check(abs(fermat_diff(p,q)) == 1,       "fermat_diff = ±1");
check(fermat_steps(p,q) <= 1,           "twins: at most one Fermat step");
check(abs(p-q) < 2^2,                   "fails kg_far(gap=2)");

\\ increment window
x = 10000; W = 80;
p2 = nextprime(x); q2 = nextprime(x + 30);
check(x <= p2 && p2 < x+W,              "p in [x, x+W)");
check(x <= q2 && q2 < x+W,              "q in [x, x+W)");
check(abs(p2-q2) < W,                   "increment_window_bound");
check(abs(p2-q2) < 2^7,                 "fails kg_far(gap=7) since W=80 < 128");

\\ shared high bits: same top bits, different lows
s = 8;
hi = 40;
p3 = hi * 2^s + 13; q3 = hi * 2^s + 97;
check(p3 \ 2^s == q3 \ 2^s,             "same quotient by 2^s");
check(abs(p3-q3) < 2^s,                 "shared_high_bits_bound");
check(isprime(101) && (101 \ 2^4) == (103 \ 2^4), "101 and 103 share bits above 2^4");
check(abs(101-103) < 2^4,               "|101-103| < 16");

\\ half-bit prefix on 20-bit primes: Fermat steps collapse
setrand(3);
n = 20; s2 = n \ 2;
hi2 = 2^(n-s2-1) + random(2^(n-s2-2));
p4 = nextprime(hi2 * 2^s2 + 1);
q4 = nextprime(hi2 * 2^s2 + 2^(s2-1));
check(p4 \ 2^s2 == q4 \ 2^s2 || abs(p4-q4) < 2^(s2+1), \
                                        "constructed pair shares a short prefix");
steps = fermat_steps(p4, q4);
ind_p = nextprime(2^(n-1) + random(2^(n-2)));
ind_q = nextprime(2^(n-1) + random(2^(n-2)));
ind_steps = fermat_steps(ind_p, ind_q);
check(steps < ind_steps,                "shared-prefix Fermat steps << independent pair");
printf("  [geom] shared-prefix steps=%d independent steps=%d\n", steps, ind_steps);

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
