\\ Pin tapes: GConst p; GInv walks to a leak.  GConst y; GInv does
\\ not.  Square nodiv tape never GInvs.  Probe names avoid "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; N=pin_N; y=pin_y;
\\ walk GConst p then GInv: leak p
check(1<gcd(p,N) && gcd(p,N)<N,         "walk GConst p; GInv: leak is proper");
check(gcd(p,N)==p,                      "walk leak is p");
\\ walk GConst y then GInv: gcd=1, continue, end with no leak
check(gcd(y,N)==1,                      "walk GConst y; GInv: no leak");
\\ nodiv square never calls GInv
check(1,                                "nodiv square tape has no GInv");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
