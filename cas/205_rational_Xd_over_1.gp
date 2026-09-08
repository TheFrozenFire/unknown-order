\\ Rational invert-all-units with Q=1 is the polynomial case:
\\ (X^d / 1)^e ≡ y on units.  Mirrors SrsaRootPoly.v.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N=pin_N; e=pin_e; d=pin_d;

same=1;
for(yy=1, N-1, \
  if(gcd(yy,N)==1, \
    Pe=lift(Mod(yy,N)^(d*e)); \
    yQe=yy*lift(Mod(1,N)^e); \
    if(Pe!=yQe%N, same=0) \
  ) \
);
check(same,                             "X^d / 1: P^e ≡ y Q^e on units");
check(lift(Mod(36,N)^d)==42,            "and is the trapdoor map at the pin y");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
