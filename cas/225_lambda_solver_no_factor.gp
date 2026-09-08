\\ lam+1 solves Strong RSA on every unit and does not split N.
\\ Mirrors pin_lambda_strong_solver.  Probe names avoid "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N=pin_N; lam=pin_lam;
oklam=1;
for(yy=1, N-1, \
  if(gcd(yy,N)==1, if(lift(Mod(yy,N)^(lam+1))!=yy, oklam=0)) \
);
check(oklam,                            "y^{lam+1} \equiv y on every unit");
check(gcd(lam+1,N)==1,                  "gcd(lam+1, N)=1, no factor");
check(lam+1>1,                          "lam+1 is a Strong-RSA exponent");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
