\\ Equal-DL public check of a tau-update.  Mirrors PotCheck.v.
\\ N=11*17=187, g=3, tau=3, rho=7.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

N = 11*17; g = 3; tau = 3; rho = 7;
pot(t, i) = lift(Mod(g, N)^(t^i));
P1 = pot(tau, 1);
Pp1 = pot(tau*rho, 1);
check(Pp1 == lift(Mod(P1, N)^rho), "P'_1 = P_1^rho");
P0 = pot(tau*rho, 0);
P1n = pot(tau*rho, 1);
P2n = pot(tau*rho, 2);
check(P1n == lift(Mod(P0, N)^(tau*rho)), "new P_1 = P_0^{tau rho}");
check(P2n == lift(Mod(P1n, N)^(tau*rho)), "new P_2 = P_1^{tau rho}");
w = 4; c = 5;
t1 = lift(Mod(P1, N)^w);
z = w + c*rho;
check(lift(Mod(P1, N)^z) == (t1 * lift(Mod(Pp1, N)^c)) % N, "Chaum-Pedersen PoK of rho");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
