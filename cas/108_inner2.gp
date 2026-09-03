\\ Inner product of two pairs.  Mirrors Inner2.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N = pin_N; g = 3;
x0 = 2; y0 = 3; x1 = 4; y1 = 5;
s = x0*y0 + x1*y1;
check(s == 26, "2*3+4*5=26");
check(lift(Mod(g,N)^s) == (lift(Mod(g,N)^(x0*y0)) * lift(Mod(g,N)^(x1*y1))) % N, \
  "g^s = g^{x0 y0} g^{x1 y1}");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
