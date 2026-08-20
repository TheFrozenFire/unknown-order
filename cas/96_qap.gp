\\ QAP completeness on committed evaluations.  Mirrors QAP.v.
\\ N=11*17=187, g=3, tau=5.  znorder(3 mod 187)=80.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

N = 11*17; g = 3; tau = 5;
evalp(cs, x) = {
  my(s = 0, p = 1, i);
  for(i = 1, length(cs), s += cs[i]*p; p *= x);
  s
};
commit(cs) = lift(Mod(g, N)^evalp(cs, tau));

\\ A=1+X, B=2, C=2+2X, H=0, Z=X.  AB-C = 0 = H Z.
A = [1, 1]; B = [2]; C = [2, 2]; H = [0]; Zpoly = [0, 1];
check(evalp(A, tau)*evalp(B, tau) - evalp(C, tau) == evalp(H, tau)*evalp(Zpoly, tau), \
  "QAP identity at tau");
Cab = commit([2, 2]); \\ A*B = 2+2X
check(Cab == (commit(C) * commit([0])) % N, "C_{A B} = C_C * C_{H Z}");

\\ two-wire: w=[1,1], A0=[1], A1=[0,1]  => Aw=[1,1]
w0 = 1; w1 = 1;
Aw = (lift(Mod(commit([1]), N)^w0) * lift(Mod(commit([0,1]), N)^w1)) % N;
check(Aw == commit(A), "specialized CRS two-wire is A_w");

\\ public io prefix
ioC = lift(Mod(commit([1]), N)^w0);
privC = lift(Mod(commit([0,1]), N)^w1);
check((ioC * privC) % N == Aw, "io * priv = full wire commit");

\\ point soundness
ordg = znorder(Mod(g, N));
check(ordg == 80, "znorder");
\\ remainder X-5 vanishes at tau=5
check(evalp([-5, 1], tau) == 0, "tau is a root of X-5");
check(commit([-5, 1]) == 1, "encoding of a root is 1");
\\ constant 80 annihilates, is not a root
check(evalp([80], tau) == 80, "constant 80 is not zero");
check(commit([80]) == 1, "g^80 = 1");
check(ordg % 80 == 0 || 80 % ordg == 0, "order divides the annihilator");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
