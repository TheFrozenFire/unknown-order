\\ Addition gate as a QAP.  Mirrors AddGate.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

N = 11*17; g = 3; tau = 5;
evalp(cs, x) = {
  my(s = 0, p = 1, i);
  for(i = 1, length(cs), s += cs[i]*p; p *= x);
  s
};
commit(cs) = lift(Mod(g, N)^evalp(cs, tau));

w0 = 3; w1 = 4; w2 = 7;
check(w0+w1 == w2, "gate sat");
check(evalp([w0+w1], tau)*1 - evalp([w2], tau) == 0, "QAP at tau");
check(commit([w0+w1]) == (lift(Mod(g,N)^w0) * lift(Mod(g,N)^w1)) % N, \
  "C_{w0+w1} = g^{w0} g^{w1}");
check(commit([w0+w1]) == (commit([w2]) * commit([0])) % N, "C_{AB} = C_C C_{HZ}");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
