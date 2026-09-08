\\ Integer cube-root of p^3 is p (GRoot leak).  Cube 8 returns 2,
\\ not a factor.  36 is not a Z-cube.  Mirrors GenericRing.v.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; N=pin_N;
check(sqrtnint(p^3, 3)==p,              "integer cube-root of p^3 is p");
check(1<p && p<N,                       "that root is a proper factor");
check(sqrtnint(8, 3)==2,                "cube-root of 8 is 2");
check(gcd(2,N)==1,                      "2 is not a factor of N");
check(ispower(36, 3)==0,                "36 is not a Z-cube");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
