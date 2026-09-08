\\ Unit GInv of y does not leak a factor.  GRoot of p^3 does.
\\ A residual solver is not a unit-GInv tape.  Mirrors
\\ pin_ginv_of_y_unit_invs / gra_root_p3_factors.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; N=pin_N; y=pin_y;
check(gcd(y,N)==1,                      "GInv of pin y: no gcd leak");
check((lift(1/Mod(y,N))*y)%N==1,        "that GInv is an inverse");
check(gcd(sqrtnint(p^3,3),N)==p,        "GRoot of p^3 still leaks p");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
