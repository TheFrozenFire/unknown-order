\\ A public-e inverter is the trapdoor; Miller-from-d still splits.
\\ The lam+1 solver does not Miller.  Not inverter/sRSA => factor.
\\ Mirrors rsa_inverter_reduced_units_constructs_factor.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; N=pin_N;
g=gcd(2^10-1, N);
check(g==p,                             "Miller-from-d gcd is p");
check(gcd(pin_lam+1, N)==1,             "lam+1 solver does not gcd-split");
check(lift(Mod(36,N)^pin_d)==42,        "public-e inverter output is y^d");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
