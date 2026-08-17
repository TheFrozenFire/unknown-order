\\ CAS witnesses — public encoding is Type A; placement is not forced.
\\ Mirrors HashSlot.v week 2.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

r = 3; s = 5; u = 7; v = 13; w = 19;
M = 4*r*s*u*v*w;
a = 13099;

found0 = 0; found2 = 0; n_pr = 0; all_ap = 1;
for(i = 0, 49, p = a + i*M; if(isprime(p), n_pr++; if(i==0, found0=1); if(i==2, found2=1); if(p%M!=a, all_ap=0)));
check(found0,                            "try-and-increment finds 13099 at i=0");
check(found2,                            "try-and-increment finds 220579 at i=2");
check(n_pr >= 2,                         "at least two primes in first 50 seeds");
check(all_ap,                            "every accepted p ≡ a (mod M)");

p0 = a + 0*M; p2 = a + 2*M;
check(!(p0 <= p2 && p2 <= 2*p0) && !(p2 <= p0 && p0 <= 2*p2), "pair_encode(0) is not balanced");
check((p2 - a) / M == 2,                 "k = 2 is public from (p, a, M)");

check(2^18 \ M + 1 == 3,                 "AP candidates in [0,2^18) about 3");
check(512 - 160 == 352,                  "public 160-bit M: 352-bit AP search");
check(isprime(19) && 19 % M != a,        "off-AP prime is not an encoding output");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
