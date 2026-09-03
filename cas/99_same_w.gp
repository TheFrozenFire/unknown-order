\\ Same witness combine check.  Mirrors SameW.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N = pin_N; g = 3; tau = 5;
evalp(cs, x) = {
  my(s = 0, p = 1, i);
  for(i = 1, length(cs), s += cs[i]*p; p *= x);
  s
};
commit(cs) = lift(Mod(g, N)^evalp(cs, tau));

\\ A0=1, A1=X; B0=2, B1=3; w=[1,4]; r=7
w0 = 1; w1 = 4; r = 7;
Aw = w0*1 + w1*tau;
Bw = w0*2 + w1*3;
CA = commit([w0, w1]);
CB = lift(Mod(g, N)^Bw);
CW = lift(Mod(g, N)^(Aw + r*Bw));
check((CA * lift(Mod(CB, N)^r)) % N == CW, "C_A * C_B^r = C_{A + r B}");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
