\\ Public-e inverter on reduced units is the trapdoor map y^d.
\\ Mirrors rsa_inverter_reduced_units_is_trapdoor.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N=pin_N; e=pin_e; d=pin_d;
inv=1;
for(yy=1, N-1, \
  if(gcd(yy,N)==1, if(lift(Mod(yy,N)^d)^e%N!=yy, inv=0)) \
);
check(inv,                              "y^d inverts e on every reduced unit");
check(lift(Mod(36,N)^d)==42,            "and inverts the pin challenge");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
