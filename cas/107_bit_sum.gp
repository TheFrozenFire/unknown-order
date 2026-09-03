\\ Little-endian bit-sum.  Mirrors BitSum.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N = pin_N; g = 3;
b0 = 1; rest = 3; \\ rest = 1 + 2*1, value of remaining bits
v = b0 + 2*rest;
check(v == 7, "1 + 2*3 = 7");
check(lift(Mod(g,N)^v) == (lift(Mod(g,N)^b0) * lift(Mod(g,N)^rest)^2) % N, \
  "g^v = g^{b0} (g^{rest})^2");
check(1 + 2*(1 + 2*1) == 7, "three bits 111");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
