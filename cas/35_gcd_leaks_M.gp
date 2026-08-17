\\ CAS — two public AP outputs leak M by gcd of differences.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

a = 13099; M = 103740;
p0 = a + 0*M; p1 = a + 1*M; p2 = a + 2*M;
check(p0 == 13099 && p2 == 220579,       "encode at k=0,2");
check((p2 - p0) % M == 0,                "M divides p2-p0");
g = gcd(p1-p0, p2-p0);
check(g % M == 0,                        "gcd of differences is a multiple of M");
check(g == M,                            "here the gcd is exactly M");
check(p0 % M == a && p2 % M == a,        "reuse recovers the residue");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
