\\ lam+1 Strong-RSA solver outputs never a proper gcd.
\\ gcd(y, N)=1 on units and gcd(lam+1, N)=1.  Miller-from-d still
\\ splits independently of the solver.  Not sRSA-solver => factor.
\\ Mirrors pin_lambda_strong_solver_outputs_never_proper_gcd.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N=pin_N; lam=pin_lam; p=pin_p;
ugcd=1;
for(yy=1, N-1, \
  if(gcd(yy,N)==1, \
    if(gcd(yy,N)==1 && gcd(lam+1,N)==1, , ugcd=0) \
  ) \
);
check(ugcd,                             "lambda solver outputs (y, lam+1) never a proper gcd");
check(gcd(lam+1, N)==1,                 "gcd(lam+1, N)=1");
check(gcd(pin_y, N)==1,                 "pin y is a unit");
check(gcd(2^10-1, N)==p,                "Miller-from-d still splits (independent of the solver)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
