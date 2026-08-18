\\ Lipmaa membership on Cl is P_Root.  Mirrors Accumulator.v.
\\ On Cl(−31) the Shanks form (2,1,4) has order 3: W^3 = id.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

D = -31;
id = qfbred(Qfb(1, D%2, (D%2-D)/4));
W = Qfb(2,1,4);
A = qfbred(W^2);
check(qfbred(W^3) == id, "W^3 = id  (membership of 3 in the identity acc)");
check(qfbred(W^2) == A, "W^2 = A  (membership of 2 in A)");
check(A != id, "A is not the identity — a proper root, not just torsion");
check(qfbclassno(D) == 3, "h(−31)=3, no trapdoor λ to delete with");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
