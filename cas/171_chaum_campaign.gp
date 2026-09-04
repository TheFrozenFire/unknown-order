\\ Chaum unblind on the campaign pin (rsa_test / pin_*), not pin187.
\\ r=2, r^{-1}=(N+1)/2 for odd N.  Mirrors shape_chaum_* in SolverShape.v.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N=pin_N; y=pin_y; x=pin_x; e=pin_e; d=pin_d;
r=2; rinv=(N+1)\2;
check(N%2==1,                           "campaign N is odd");
check((r*rinv)%N==1,                    "r=2 inverse is (N+1)/2");
check(gcd(r,N)==1,                      "blinder 2 is a unit");
blinded=lift(Mod(y,N)*Mod(r,N)^e);
signed=lift(Mod(blinded,N)^d);
unblind=lift(Mod(signed,N)*Mod(rinv,N));
raw=lift(Mod(y,N)^d);
check(unblind==raw,                     "unblind(sign(y·2^e)) = y^d");
check(raw==x,                           "y^d is leftover x");
check(e==pin_e,                         "protocol e is campaign e");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
