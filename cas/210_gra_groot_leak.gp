\\ GConst p^3 then GRoot leaks p.  GConst 8 then GRoot is 2, no leak.
\\ Mirrors gra_root_p3_factors.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; N=pin_N;
rp=sqrtnint(p^3, 3);
check(rp==p && gcd(rp, N)==p,           "GConst p^3; GRoot leaks p");
check(sqrtnint(8, 3)==2,                "GConst 8; GRoot is 2");
check(gcd(2,N)==1,                      "that 2 does not leak");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
