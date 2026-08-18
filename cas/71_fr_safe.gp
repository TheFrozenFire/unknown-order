\\ Franklin–Reiter cube gap and safe-prime λ.  Mirrors SmallExponent / StrongPrimes.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

m = 5; delta = 3;
check((m+delta)^3 - m^3 == 3*delta*m*(m+delta) + delta^3, "cube gap identity");
N = 187;
check(((m+delta)^3 - m^3) % N == (3*delta*m*(m+delta)+delta^3) % N, "cube gap mod N");

p = 23; q = 47;
check(isprime(p) && isprime((p-1)/2), "23 is safe");
check(isprime(q) && isprime((q-1)/2), "47 is safe");
check(lcm(p-1,q-1) == 2*((p-1)/2)*((q-1)/2), "λ(safe,safe)=2 p' q'");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
