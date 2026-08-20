\\ Mux s a b.  Mirrors Mux.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

mux(s, a, b) = s*a + (1-s)*b;
check(mux(0, 7, 9) == 9, "s=0 selects b");
check(mux(1, 7, 9) == 7, "s=1 selects a");
a = 7; b = 9; s = 1; out = mux(s,a,b);
check(s*a + b == out + s*b, "s a + b = out + s b");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
