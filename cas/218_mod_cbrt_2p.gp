\\ Modular cube-root of 2p is 11, gcd p.  Same leak as GInv of a
\\ non-unit: the output gcd is the factor.  Mirrors SrsaModCbrt.v.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; N=pin_N;
h=2*p;
check(gcd(h,N)==p,                      "gcd(2p,N)=p");
check(lift(Mod(p,N)^3)==h%N,            "p^3 \equiv 2p (mod N)");
check(gcd(p,N)==p,                      "cube-root output gcd is p");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
