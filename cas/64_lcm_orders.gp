\\ Two orders' lcm is not λ.  Mirrors Order.v lcm_two_order2_not_lambda.
\\ Completeness (lcm of *enough* orders) stays in 25_order.gp.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

N = 187; lam = lcm(10,16);
check(lam == 80, "λ(11·17)=80");
check(znorder(Mod(-1,N))==2, "ord(−1)=2");
check(znorder(Mod(67,N))==2, "ord(67)=2  (mixed √1)");
check(lcm(2,2) != lam, "lcm of two 2-Sylow orders is not λ");
check(lift(Mod(67,N)^2)==1 && 67 != 1 && 67 != N-1, "67 is the mixed root");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
