\\ e-th root of a non-unit carries the same proper gcd.
\\ Mirrors eth_root_nonunit_factors.  Probe names avoid "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; N=pin_N; e=pin_e;
r=165;
check(lift(Mod(r,N)^e)==p,              "165^e \equiv p (mod N)");
check(gcd(r,N)==gcd(p,N),               "output gcd equals input gcd");
check(gcd(r,N)==p,                      "that gcd is p");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
