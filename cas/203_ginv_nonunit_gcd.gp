\\ GInv of a non-unit handle returns gcd(h,N), a proper factor.
\\ GInv of a unit returns a modular inverse, not a leak.
\\ Mirrors GenericRing.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; y=pin_y;

check(gcd(p,N)==p,                      "gcd(p,N)=p");
check(1<p && p<N,                       "p is a proper factor");
check(gcd(2*p,N)==p,                    "gcd(2p,N)=p");
check(gcd(y,N)==1,                      "gcd(y,N)=1");
check(lift(Mod(y,N)*Mod(y,N)^(-1))==1,  "unit inverse: y·y^{-1}≡1");
check(gcd(0,N)==N,                      "gcd(0,N)=N is not proper");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
