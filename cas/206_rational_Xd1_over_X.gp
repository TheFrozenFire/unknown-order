\\ Rational invert-all-units: P=X^{d+1}, Q=X.  P/Q = X^d on units
\\ (y≠0).  P^e ≡ y Q^e.  Mirrors SrsaRootPoly.v.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N=pin_N; e=pin_e; d=pin_d;

same=1; mapd=1;
for(yy=1, N-1, \
  if(gcd(yy,N)==1, \
    Pe=lift(Mod(yy,N)^((d+1)*e)); \
    yQe=yy*lift(Mod(yy,N)^e); \
    if(Pe!=yQe%N, same=0); \
    ratio=lift(Mod(yy,N)^(d+1)/Mod(yy,N)); \
    if(ratio!=lift(Mod(yy,N)^d), mapd=0) \
  ) \
);
check(same,                             "X^{d+1}/X: P^e ≡ y Q^e on units");
check(mapd,                             "X^{d+1}/X = X^d on units");
check(gcd(36,N)==1,                     "Q(y)=y is a unit at the pin");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
