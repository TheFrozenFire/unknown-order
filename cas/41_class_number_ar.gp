\\ CAS witnesses — class number is an AR-search trapdoor on Cl(−31).
\\ h(−31)=3 annihilates every reduced class; y^{h} = 1 ⇒ taking a
\\ square (2 inverse mod 3) or y^{h+1}=y solves adaptive-root search.
\\ Mirrors ClassGroupWall / Hardness annihilator + fractional-root arrows.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

id = qfbred(Qfb(1,1,8));
f = Qfb(2,1,4);
inv = Qfb(2,-1,4);
sq = Qfb(2,-1,4);

check(qfbclassno(-31) == 3, "h(-31)=3");
check(qfbred(id^3) == id, "id^3 = id");
check(qfbred(f^3) == id, "f^3 = id");
check(qfbred(inv^3) == id, "inv^3 = id");
check(qfbred(f^4) == f, "f^{h+1} = f");
check(qfbred(inv^2) == f, "(f^{-1})^2 = f  (2 invertible mod 3)");
check(qfbred(f^2) == inv, "f^2 = f^{-1}");
check(qfbred(id^4) == id, "id^{h+1} = id");

\\ Order assumption: a multiple of the order annihilates.
check(qfbred(f^6) == id, "f^6 = id (multiple of ord=3)");
check(qfbred(f^0) == id, "f^0 = id");

\\ Fractional root: x^a = y^b.  RSA is b=1; annihilator is y=id, b=0-ish.
check(qfbred(inv^2) == qfbred(f^1), "inv^2 = f^1 (fractional root)");
check(qfbred(f^2) == qfbred(inv^1), "f^2 = inv^1");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
