\\ Per-slot coefficient PoK and assemble.  Mirrors CoeffPoK.v.
\\ N = pin_N=187, g=3, tau=5.

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
slot(ii, a) = lift(Mod(g, N)^((tau^ii)*a));

a0 = 2; a1 = 3; a2 = 1;
C = commit([a0, a1, a2]);
Q0 = slot(0, a0); Q1 = slot(1, a1); Q2 = slot(2, a2);
check((Q0*Q1*Q2)%N == C, "assemble slots = pot_poly");

\\ Schnorr on slot 1
P1 = lift(Mod(g, N)^tau);
s = 4; ch = 5; z = s + ch*a1;
t1 = lift(Mod(P1, N)^s);
check(lift(Mod(P1, N)^z) == (t1 * lift(Mod(Q1, N)^ch)) % N, "slot-1 eqdl");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
