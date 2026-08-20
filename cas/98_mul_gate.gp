\\ One multiplication gate as a QAP.  Mirrors MulGate.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

N = 11*17; g = 3; tau = 5;
evalp(cs, x) = {
  my(s = 0, p = 1, i);
  for(i = 1, length(cs), s += cs[i]*p; p *= x);
  s
};
commit(cs) = lift(Mod(g, N)^evalp(cs, tau));

w0 = 3; w1 = 4; w2 = 12;
check(w0*w1 == w2, "gate sat");
Aw = [w0]; Bw = [w1]; Cw = [w2];
H = [0]; van = [0, 1];
check(evalp(Aw, tau)*evalp(Bw, tau) - evalp(Cw, tau) == evalp(H, tau)*evalp(van, tau), \
  "QAP at tau for the mul gate");
check(commit([w0*w1]) == (commit(Cw) * commit([0])) % N, "C_{AB} = C_C C_{HZ}");

check(0*0 == 0 && 1*1 == 1, "bit square");
check(evalp([0], tau)*evalp([0], tau) - evalp([0], tau) == 0, "bit 0 QAP");
check(evalp([1], tau)*evalp([1], tau) - evalp([1], tau) == 0, "bit 1 QAP");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
