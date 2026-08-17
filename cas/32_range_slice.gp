\\ CAS — S_b <-> [k_min, k_max].  Mirrors Derive.v area 1.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

aa = 13099; MM = 103740;
b = 18; lo = 2^(b-1); hi = 2^b;
check(lo == 131072 && hi == 262144,      "b=18 range [2^17, 2^18)");
k0 = (lo - aa + MM - 1) \ MM;
k1 = (hi - 1 - aa) \ MM;
check(k0 <= k1,                          "slice nonempty at b=18");
all = 1; n = 0;
for(k = k0, k1, p = aa + k*MM; if(!(lo <= p && p < hi && (p-aa)%MM==0), all=0); n++);
check(all,                               "every k in [kmin,kmax] lands in S_b");
check(n == k1-k0+1,                      "|S_b| = kmax-kmin+1");

b2 = 20; lo2 = 2^(b2-1); hi2 = 2^b2;
k02 = (lo2 - aa + MM - 1) \ MM;
k12 = (hi2 - 1 - aa) \ MM;
check(k02 <= k12,                        "slice nonempty at b=20");

check((512 + 1048576 - 1) \ 1048576 > 1023 \ 1048576, "M=2^20, b=10: empty slice");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
