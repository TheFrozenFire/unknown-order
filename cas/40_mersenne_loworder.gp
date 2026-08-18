\\ CAS witnesses — 2020/1310 pin: Mersenne discriminant Δ = 1−2^p
\\ (here p = 5, Δ = −31) carries a reduced form of odd order 3
\\ that is not ambiguous.  That wins restricted low-order after
\\ excluding Cl[2].  Mirrors ClassGroupWall.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

idform(D) = qfbred(Qfb(1, D%2, (D%2 - D)/4));

form_order(f, D) = {
  my(id = idform(D), g = qfbred(f), n = 1);
  while(g != id && n < 200, g = qfbred(g*f); n++);
  n
};

is_amb_red(f) = {
  my(a = component(f,1), b = component(f,2), c = component(f,3));
  b == 0 || a == b || a == -b || a == c
};

\\ Shanks / 2020/1310: Δ = 2^p − 1 Mersenne, form (2, 1, 2^{p−3}).
p = 5;
M = 2^p - 1;
D = -M;
f = Qfb(2, 1, 2^(p-3));
check(M == 31, "Mersenne 2^5-1 = 31");
check(D == -31, "discriminant -31");
check(component(f,1)==2 && component(f,2)==1 && component(f,3)==4, "Shanks form (2,1,4)");
check(qfbred(f) == f, "(2,1,4) is reduced");
check(!is_amb_red(f), "(2,1,4) is not ambiguous");
check(form_order(f, D) == 3, "order of (2,1,4) on Cl(-31) is 3");
check(qfbred(f^3) == idform(D), "f^3 reduces to the identity");
check(qfbred(f^2) != idform(D), "f^2 is not the identity");
check(qfbclassno(D) == 3, "h(-31) = 3");
check(qfbclassno(D) % 2 == 1, "class number is odd (no extra 2-torsion)");

\\ Theorem 1 of 2020/1310: D = 4u^3 − 1, form (u, 1, u^2), order 3.
u = 2;
check(4*u^3 - 1 == 31, "u=2 is the Mersenne case of Thm 1");
g = Qfb(3, 1, 9);
check(1 - 4*3*9 == -107, "u=3 has disc -107");
check(form_order(g, -107) == 3, "order of (3,1,9) on Cl(-107) is 3");
check(!is_amb_red(g), "(3,1,9) is not ambiguous");
check(qfbred(g^3) == idform(-107), "(3,1,9)^3 reduces to the identity");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
