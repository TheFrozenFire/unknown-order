\\ Unique unit cube-root on the pin (gcd(3,\955)=1).  Equals y^d.
\\ Mirrors SrsaModCbrt.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N=pin_N; e=pin_e; d=pin_d;
uniq=1; mapd=1;
for(yy=1, N-1, \
  if(gcd(yy,N)==1, \
    c=0; \
    for(r=0, N-1, if(gcd(r,N)==1 && lift(Mod(r,N)^e)==yy, c++)); \
    if(c!=1, uniq=0); \
    if(lift(Mod(yy,N)^d)^e%N!=yy, mapd=0) \
  ) \
);
check(uniq,                             "unique unit cube-root of every unit");
check(mapd,                             "that root is y^d");
check(gcd(e, pin_lam)==1,               "gcd(e, lam)=1 so cubing is bijective");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
