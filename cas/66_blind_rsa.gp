\\ Chaum blinded RSA.  Mirrors BlindRSA.v.  rsa_test 11·17, e=3, d=27.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 11; q = 17; N = p*q; e = 3; d = 27;
m = 42; r = 5;
check(gcd(r,N)==1, "blinder is a unit");
blinded = lift(Mod(m,N) * Mod(r,N)^e);
signed = lift(Mod(blinded,N)^d);
rinv = lift(1/Mod(r,N));
unblind = lift(Mod(signed,N)*Mod(rinv,N));
raw = lift(Mod(m,N)^d);
check(unblind == raw, "unblind(sign(m·r^e)) = m^d");
check(signed == lift(Mod(raw,N)*Mod(r,N)), "blinded signature is raw·r");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
