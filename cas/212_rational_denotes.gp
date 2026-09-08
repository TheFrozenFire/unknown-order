\\ Unit-GInv denotation: y^{d+1} * y^{-1} = y^d on units, which is
\\ the rational X^{d+1}/X.  Mirrors gra_unit_inv_denotes.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N=pin_N; d=pin_d;

same=1;
for(yy=1, N-1, \
  if(gcd(yy,N)==1, \
    num=lift(Mod(yy,N)^(d+1)); \
    den=yy; \
    invden=lift(1/Mod(den,N)); \
    if((num*invden)%N!=lift(Mod(yy,N)^d), same=0) \
  ) \
);
check(same,                             "y^{d+1} * y^{-1} = y^d on units");
check(gcd(36,N)==1,                     "pin y is a unit denominator");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
