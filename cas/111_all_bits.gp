\\ Three-bit value encoding.  Mirrors AllBits.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

N = 11*17; g = 3;
b0 = 1; b1 = 0; b2 = 1;
v = b0 + 2*(b1 + 2*b2);
check(v == 5, "101 = 5");
inner = (lift(Mod(g,N)^b1) * lift(Mod(g,N)^b2)^2) % N;
check(lift(Mod(g,N)^v) == (lift(Mod(g,N)^b0) * inner^2) % N, \
  "g^v = g^{b0} (g^{b1} (g^{b2})^2)^2");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
