\\ Modular cube-root of the pin unit y is x=42, a unit.
\\ That is a residual leaf at e=3, not a gcd leak.
\\ Mirrors SrsaModCbrt.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N=pin_N; y=pin_y; x=pin_x; e=pin_e; lam=pin_lam;
check(lift(Mod(x,N)^e)==y,              "x^e \equiv y (mod N)");
check(gcd(x,N)==1,                      "that root is a unit");
check(gcd(e,lam)==1,                    "gcd(e, lam)=1");
check((e-1)%lam!=0,                     "lam does not divide e-1");
check(e%2==1,                           "e is odd");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
