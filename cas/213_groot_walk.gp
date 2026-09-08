\\ Walking a tape: GConst p^3 then GRoot leaks p; GConst 8 then
\\ GRoot does not.  Mirrors gra_first_root_factor.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; N=pin_N;
rp=sqrtnint(p^3, 3);
check(1<gcd(rp,N) && gcd(rp,N)<N,       "walk GConst p^3; GRoot: leak is proper");
check(gcd(rp,N)==p,                     "walk leak is p");
check(gcd(sqrtnint(8,3),N)==1,          "walk GConst 8; GRoot: no leak");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
