\\ Aux self-bilinear spec, evaluated via discrete logs in <g>.
\\ Mirrors AuxBil.v.  znlog is not a construction; it pins the identity.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N = pin_N;
g = 3;
tau = 5;
ordg = znorder(Mod(g, N));
check(ordg == 80, "znorder(3 mod 187) = 80");

dlog(x) = znlog(Mod(x, N), Mod(g, N));
\\ e(aux, X, Y) = e(aux,g,g)^{dlog X * dlog Y}, with e(aux,g,g) = g
eg = g;
e(X, Y) = lift(Mod(eg, N)^(dlog(X)*dlog(Y)));

check(e(lift(Mod(g,N)^2), lift(Mod(g,N)^3)) == lift(Mod(eg,N)^(2*3)), \
  "self-bil on exponents 2,3");
check(e(g, g) == g % N, "e(g,g) = g");

pot(ii) = lift(Mod(g, N)^(tau^ii));
check(e(pot(0), pot(1)) == pot(1), "e(P_0, P_1) = P_1");
check(e(pot(1), pot(1)) == pot(2), "e(P_1, P_1) = P_2  (evaluates)");
check(e(pot(2), pot(1)) == pot(3), "e(P_2, P_1) = P_3  (publishes next)");
check(e(pot(2), pot(1)) == e(pot(3), pot(0)), "checks consecutive powers");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
