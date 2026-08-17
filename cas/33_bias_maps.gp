\\ CAS — seed mod L is uneven; force-residue can leave the range.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

D = 10; L = 6;
c0 = 0; c5 = 0;
for(s = 0, D-1, if(s%L==0, c0++); if(s%L==5, c5++));
check(c0 == 2 && c5 == 1,                "mod 6 on 0..9: 0 hit twice, 5 once");
check(D % L != 0,                        "L does not divide the domain");

n = 15; aa = 3; MM = 5;
fr = n - n%MM + aa;
check(8 <= n && n < 16,                  "15 is in [2^3, 2^4)");
check(fr == 18 && !(8 <= fr && fr < 16), "force residue leaves the range");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
