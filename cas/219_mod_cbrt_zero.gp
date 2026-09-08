\\ Modular cube-root of 0 is 0; gcd(0,N)=N is not a proper factor.
\\ Mirrors SrsaModCbrt.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N=pin_N;
check(lift(Mod(0,N)^3)==0,              "0^3 \equiv 0 (mod N)");
check(gcd(0,N)==N,                      "gcd(0,N)=N is not proper");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
