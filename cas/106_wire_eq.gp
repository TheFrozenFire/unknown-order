\\ Wire equality.  Mirrors WireEq.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N = pin_N; g = 3;
w0 = 5; w1 = 5;
check(w0 + 0 == w1, "w0 + 0 = w1");
check(lift(Mod(g,N)^w0) == lift(Mod(g,N)^w1), "same encoding");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
