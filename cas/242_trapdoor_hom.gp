\\ Trapdoor y |-> y^d is a group hom on units.  Mixed cube-root of
\\ 36 with 7th-root of 2 is not: 42 * 2^23 cong 72, not a 7th or
\\ cube root of 72.  Mirrors residual_x_homomorphic of the trapdoor
\\ inhabitant.  Not residual-solver => factor.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N=pin_N; d=pin_d;

hom=1;
for(y1=1, N-1, \
  if(gcd(y1,N)==1, \
    for(y2=1, N-1, \
      if(gcd(y2,N)==1, \
        x1=lift(Mod(y1,N)^d); x2=lift(Mod(y2,N)^d); \
        y12=lift(Mod(y1*y2,N)); x12=lift(Mod(y12,N)^d); \
        if(lift(Mod(x1*x2,N))!=x12, hom=0) \
      ) \
    ) \
  ) \
);
check(hom,                              "trapdoor is a hom on units");

prd=lift(Mod(42*lift(Mod(2,N)^23),N));
check(prd==72,                          "42 * 2^23 cong 72");
check(lift(Mod(72,N)^d)!=prd,           "72^d is not that product");
check(lift(Mod(72,N)^23)!=prd,          "72^23 is not that product");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
