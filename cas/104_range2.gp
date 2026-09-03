\\ Two-bit value from bits.  Mirrors Range2.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N = pin_N; g = 3;
b0 = 1; b1 = 1; v = b0 + 2*b1;
check(v == 3, "1 + 2*1 = 3");
check(lift(Mod(g,N)^v) == (lift(Mod(g,N)^b0) * lift(Mod(g,N)^b1)^2) % N, \
  "g^v = g^{b0} (g^{b1})^2");
b0 = 0; b1 = 1; v = b0 + 2*b1;
check(v == 2, "0 + 2*1 = 2");
check(lift(Mod(g,N)^v) == (lift(Mod(g,N)^b0) * lift(Mod(g,N)^b1)^2) % N, \
  "encoding of 2");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
