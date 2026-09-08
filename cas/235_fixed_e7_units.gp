\\ Unique unit 7th root: y |-> y^23 inverts cubing-at-7 on every unit.
\\ Mirrors unique_unit_eth_root_inv / trapdoor_eth_inverts at e=7.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N=pin_N; e=7; d=23;
okx=1;
for(yy=1, N-1, \
  if(gcd(yy,N)==1, \
    xd=lift(Mod(yy,N)^d); \
    if(lift(Mod(xd,N)^e)!=yy, okx=0) \
  ) \
);
check(okx,                              "y^23 is a 7th root on every unit");
check(gcd(23,N)==1,                     "inverse 23 is a unit of N");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
