\\ N+1 is coprime but not a residue, so not an RSA / Strong-RSA
\\ problem.  Mirrors rsa_problem_y_is_residue.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N=pin_N; e=pin_e;
check(gcd(N+1,N)==1,                    "N+1 is coprime");
check(lift(Mod(42,N)^e)!=N+1,           "a residue e-th power is not N+1");
check(lift(Mod(36,N)^(pin_lam+1))!=N+1, "a residue Strong-RSA witness is not N+1");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
