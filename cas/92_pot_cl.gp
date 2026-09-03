\\ tau-string on Cl(-31).  Mirrors PotCl.v.
\\ Shanks form (2,1,4) has order 3.  Public annihilator is 2, not lambda.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

D = -31;
id = qfbred(Qfb(1, D%2, (D%2-D)/4));
gg = Qfb(2,1,4);
check(qfbred(gg^3) == id, "g^3 = id");
check(qfbclassno(D) == 3, "h(-31)=3, no lambda trapdoor");

tau = 2;
P0 = qfbred(gg^(tau^0));
P1 = qfbred(gg^(tau^1));
P2 = qfbred(gg^(tau^2));
check(P0 == qfbred(gg), "P_0 = g");
check(P1 == qfbred(gg^2), "P_1 = g^tau");
check(P2 == qfbred(gg^4), "P_2 = g^{tau^2}");
check(qfbred(P0^tau) == P1, "P_1 = P_0^tau");
check(qfbred(P1^tau) == P2, "P_2 = P_1^tau");

\\ contribute rho at slot 0 is identity
rho = 2;
check(qfbred(P0^(rho^0)) == P0, "contribute at slot 0 is identity");

\\ RSA presentation of the same string
N = pin_N; gZ = 3;
check(lift(Mod(gZ, N)^(tau^0)) == gZ % N, "RSA P_0 = g");
check(lift(Mod(gZ, N)^(tau^1)) == lift(Mod(gZ, N)^tau), "RSA P_1 = g^tau");
left = lift(Mod(lift(Mod(gZ, N)^(tau^2)), N)^(rho^2));
right = lift(Mod(gZ, N)^((tau*rho)^2));
check(left == right, "RSA contribute multiplies tau");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
