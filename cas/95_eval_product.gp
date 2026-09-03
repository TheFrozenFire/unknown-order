\\ Product of committed evaluations at tau.  Mirrors EvalProduct.v.
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

a = [2, 3];
b = [1, 4];
\\ conv: (2+3X)(1+4X) = 2 + 11 X + 12 X^2
ab = [2, 11, 12];
ea = evalp(a, tau); eb = evalp(b, tau); eab = evalp(ab, tau);
check(ea == 2+3*tau, "eval a");
check(eb == 1+4*tau, "eval b");
check(eab == ea*eb, "eval(conv) = eval a * eval b");

Ca = commit(a); Cb = commit(b); Cab = commit(ab);
check(lift(Mod(Ca, N)^eb) == Cab, "C_a^{b(tau)} = C_{a*b}");
check(lift(Mod(Cb, N)^ea) == Cab, "C_b^{a(tau)} = C_{a*b}");
check((Ca*Cb)%N == commit([2+1, 3+4]), "C_a * C_b = C_{a+b}, not C_{a*b}");
check((Ca*Cb)%N != Cab, "group product is not the field product");

\\ monomials: tau^i * tau^j = tau^{i+j} lives at P_{i+j}
ii = 2; jj = 3;
Pii = lift(Mod(g, N)^(tau^ii));
Pjj = lift(Mod(g, N)^(tau^jj));
Psum = lift(Mod(g, N)^(tau^(ii+jj)));
check(Psum == lift(Mod(g, N)^((tau^ii)*(tau^jj))), "P_{i+j} = g^{tau^i * tau^j}");
check((Pii*Pjj)%N != Psum, "P_i * P_j is not P_{i+j}");

\\ shift: X*a = [0,2,3]
sh = [0, 2, 3];
check(evalp(sh, tau) == tau*ea, "eval(X f) = tau * eval f");
check(commit(sh) == lift(Mod(Ca, N)^tau), "C_{X f} = C_f^tau");

\\ two-wire
w0 = 2; w1 = 3;
A0 = [1, 0]; A1 = [0, 1];
Cw = (lift(Mod(commit(A0), N)^w0) * lift(Mod(commit(A1), N)^w1)) % N;
comb = [w0, w1];
check(Cw == commit(comb), "two-wire commit is g^{(w0 A0 + w1 A1)(tau)}");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
