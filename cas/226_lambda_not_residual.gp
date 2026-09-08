\\ lam | ((lam+1)-1), so the lam+1 witness is not a residual leaf.
\\ Mirrors lambda_plus_one_not_residual_leaf.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

lam=pin_lam;
check((lam+1-1)%lam==0,                 "lam divides (lam+1)-1");
check(gcd(pin_e, lam)==1,               "public e is coprime to lam");
check((pin_e-1)%lam!=0,                 "public e is a residual exponent");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
