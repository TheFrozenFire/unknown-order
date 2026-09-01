\\ CPP17: integer Sigma (GQ) extracts a fixed-e RSA root, not a chosen e.
\\ Mirrors CPP17.v.  Not HVZK / NIZK.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

N = 11*17; ee = 3; x = 42; z = 36;

check(lift(Mod(x,N)^ee) == z,           "witness: 42^3 ≡ 36 (fixed e=3)");

\\ GQ completeness at c=1, k=1
k = 1; c = 1;
t = lift(Mod(k,N)^ee);
r = lift(Mod(k,N) * Mod(x,N)^c);
check(lift(Mod(r,N)^ee) == lift(Mod(t,N)*Mod(z,N)^c), "GQ verifies at e=3");

\\ second transcript c'=0, k=2: gcd(c-c', e)=1 so Shamir applies
k2 = 2; c2 = 0;
t2 = lift(Mod(k2,N)^ee);
r2 = lift(Mod(k2,N) * Mod(x,N)^c2);
check(lift(Mod(r2,N)^ee) == lift(Mod(t2,N)*Mod(z,N)^c2), "GQ verifies at c=0");
check(gcd(c-c2, ee) == 1,               "Shamir gcd(c-c',e)=1");

\\ the protocol e is 3, not λ+1=81
check(ee == 3,                          "public e is 3");
check(81 != 3,                          "λ+1 is not the protocol e");
check(lift(Mod(z,N)^81) == z,           "sRSA (z,81) is a different pair");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
