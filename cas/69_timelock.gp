\\ RSW time-lock trapdoor.  Mirrors TimeLock.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 11; q = 17; N = p*q; lam = lcm(10,16);
a = 3; T = 10;
slow = lift(Mod(a,N)^(2^T));
fast = lift(Mod(a,N)^((2^T) % lam));
check(slow == fast, "a^{2^T} = a^{2^T mod λ} on units");
check((2^T) % lam < lam, "reduced exponent is shorter");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
