\\ Modular cube-root of p is 165, gcd 11.  165^3 \equiv p (mod N).
\\ Distinct from integer cube-root.  Mirrors SrsaModCbrt.v.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; N=pin_N;
r=165;
check(lift(Mod(r,N)^3)==p,              "165^3 \equiv p (mod N)");
check(gcd(r,N)==p,                      "gcd(165,N)=p");
check(1<gcd(r,N) && gcd(r,N)<N,         "that gcd is a proper factor");
check(r!=p,                             "modular root is not p itself");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
