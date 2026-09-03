\\ Equal-DL ladder for extra CRS powers.  Mirrors PotLadder.v.
\\ N = pin_N=187, g=3, tau=3, rho=7.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N = pin_N; g = 3; tau = 3; rho = 7;
pot(t, ii) = lift(Mod(g, N)^(t^ii));
P1 = pot(tau, 1); Pp1 = pot(tau*rho, 1);
P2 = pot(tau, 2); Pp2 = pot(tau*rho, 2);
P3 = pot(tau, 3); Pp3 = pot(tau*rho, 3);
A = lift(Mod(P2, N)^rho);
check(Pp1 == lift(Mod(P1, N)^rho), "P'_1 = P_1^rho");
check(lift(Mod(A, N)^rho) == Pp2, "A^rho = P'_2");
check(Pp2 == lift(Mod(P2, N)^(rho^2)), "P'_2 = P_2^{rho^2}");

ladder(P, k) = lift(Mod(P, N)^(rho^k));
check(ladder(P2, 0) == P2 % N, "ladder_0 = P_2");
check(ladder(P2, 1) == A, "ladder_1 = A");
check(ladder(P2, 2) == Pp2, "ladder_2 = P'_2");
check(ladder(P3, 3) == Pp3, "ladder on P_3 of length 3 is P'_3");
check(ladder(P2, 3) != Pp3, "wrong-length ladder is not P'_3");

w = 4; c = 5; z = w + c*rho;
t1 = lift(Mod(P1, N)^w); t2 = lift(Mod(P2, N)^w);
check(lift(Mod(P1, N)^z) == (t1 * lift(Mod(Pp1, N)^c)) % N, "leg1 eqdl on P_1");
check(lift(Mod(P2, N)^z) == (t2 * lift(Mod(A, N)^c)) % N, "leg1 eqdl on P_2");
t2b = lift(Mod(A, N)^w);
check(lift(Mod(P1, N)^z) == (t1 * lift(Mod(Pp1, N)^c)) % N, "leg2 eqdl on P_1");
check(lift(Mod(A, N)^z) == (t2b * lift(Mod(Pp2, N)^c)) % N, "leg2 eqdl on A");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
