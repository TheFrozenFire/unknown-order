\\ Walking a tape: GConst p then GInv leaks p; GConst y then GInv
\\ does not leak.  Mirrors gra_first_inv_gcd.  Probe names avoid
\\ the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; N=pin_N; y=pin_y;

\\ init [0,1,y]; GConst p → handle 3 = p; GInv 3 → gcd(p,N)=p
check(gcd(p,N)==p && 1<p && p<N,        "GConst p; GInv leaks p");
\\ GConst y → handle 3 = y; GInv 3 → gcd=1, no proper leak
check(gcd(y,N)==1,                      "GConst y; GInv does not leak");
check(lift((1/Mod(y,N))*Mod(y,N))==1,   "that inverse is a unit");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
