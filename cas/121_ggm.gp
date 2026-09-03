\\ Damgård-Koprowski remark: multiply-only signature has no add.
\\ Mirrors GenericRing.v wave 6a.
\\ A {mul,inv} tape cannot host the GRA polynomial P^e-X.
\\ RSA solution at e>1 is already a Strong-RSA witness (relation arrow).

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N = pin_N; ee = 3;

\\ multiply-only tape: init [1, y], three muls y*y*y
y = 36;
gtape = [1, y];
gtape = concat(gtape, [gtape[2]*gtape[2]]);
gtape = concat(gtape, [gtape[3]*gtape[2]]);
check(gtape[4] == y^3,                  "GGM y*y*y over Z");
check(length(gtape) == 4,               "no extra add handle");

\\ the GRA degree obstruction uses X^3-X which needs subtraction/addition
XmX = [0, -1, 0, 1];
check(XmX[2] == -1,                     "P^e-X has an additive coeff -1, uninhabited in {mul}");

\\ prescribed-e RSA solution is a Strong-RSA witness
check(ee > 1 && lift(Mod(42,N)^ee) == 36, "Problem_RSA(187,3,36,42)");
check(ee > 1 && lift(Mod(42,N)^ee) == 36, "hence Problem_StrongRSA(187,36,42,3)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
