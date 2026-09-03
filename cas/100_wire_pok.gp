\\ Wire PoK on a specialized CRS.  Mirrors WirePoK.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N = pin_N; g = 3; tau = 5;
evalp(cs, x) = {
  my(s = 0, p = 1, i);
  for(i = 1, length(cs), s += cs[i]*p; p *= x);
  s
};
U(A) = lift(Mod(g, N)^evalp(A, tau));
slot(A, ww) = lift(Mod(U(A), N)^ww);

w0 = 2; w1 = 3; w2 = 1;
A0 = [1]; A1 = [0, 1]; A2 = [1, 1];
Q0 = slot(A0, w0); Q1 = slot(A1, w1); Q2 = slot(A2, w2);
Cw = (Q0*Q1*Q2)%N;
want = lift(Mod(g, N)^(w0*evalp(A0,tau) + w1*evalp(A1,tau) + w2*evalp(A2,tau)));
check(Cw == want, "assemble wire slots = pot_wires");

s = 4; ch = 6; z = s + ch*w1;
t1 = lift(Mod(U(A1), N)^s);
check(lift(Mod(U(A1), N)^z) == (t1 * lift(Mod(Q1, N)^ch)) % N, "wire-1 eqdl");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
