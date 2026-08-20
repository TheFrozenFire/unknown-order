\\ Conditional swap.  Mirrors CondSwap.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

mux(s,a,b) = s*a+(1-s)*b;
check(mux(0,9,3)==3 && mux(0,3,9)==9, "s=0 selects b");
check(mux(1,9,3)==9 && mux(1,3,9)==3, "s=1 selects a");
a = 7; b = 4; s = 1;
ap = mux(s,b,a); bp = mux(s,a,b);
check(ap==b && bp==a, "swap");
check(mux(s,bp,ap)==a && mux(s,ap,bp)==b, "involution");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
