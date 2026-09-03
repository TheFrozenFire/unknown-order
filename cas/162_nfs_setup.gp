\\ NFS setup identity: two integer polynomials sharing a root m mod N.
\\ Evaluation f(m) ≡ 0 (mod N) is the resultant of f and (x-m).
\\ Homogenised remainder: F(a,b) − f(m) b^2 = (a−m b) H(a,b),
\\ so F ≡ G H (mod N).  Irreducible companion x^2+x+5 at m=13
\\ (disc −19).  Reducible x^2+8x+7 at m=10 is the two-sided pin
\\ of cas/163; the identity does not need a field.
\\ Mirrors SieveRelation.v nfs_eval_* / hom_quad_remainder.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

N = 11*17;
firr(x) = x^2 + x + 5;
fred(x) = x^2 + 8*x + 7;
Firr(a, b) = a^2 + a*b + 5*b^2;
Fred(a, b) = a^2 + 8*a*b + 7*b^2;
Girr(a, b) = a - 13*b;
Hirr(a, b) = a + 14*b;
Gred(a, b) = a - 10*b;
Hred(a, b) = a + 18*b;

check(firr(13) == N,                      "f_irr(13)=187");
check(fred(10) == N,                      "f_red(10)=187");
check(firr(13) % N == 0,                  "common root 13 of f_irr and x-13");
check(fred(10) % N == 0,                  "common root 10 of f_red and x-10");
check(issquare(1-4*5) == 0,               "disc(f_irr)=−19, no square");
check(fred(-1) == 0 && fred(-7) == 0,     "f_red=(x+1)(x+7) over Z");

\\ remainder identity on several (a,b)
check(Firr(2,1) - firr(13)*1 == Girr(2,1)*Hirr(2,1), "irr remainder (2,1)");
check(Firr(-5,1) - firr(13) == Girr(-5,1)*Hirr(-5,1), "irr remainder (−5,1)");
check(Fred(-15,1) - fred(10) == Gred(-15,1)*Hred(-15,1), "red remainder (−15,1)");
check(Fred(-6,1) - fred(10) == Gred(-6,1)*Hred(-6,1), "red remainder (−6,1)");
check(Firr(3,2) % N == (Girr(3,2)*Hirr(3,2)) % N, "F ≡ GH (mod N) irr (3,2)");
check(Fred(1,1) % N == (Gred(1,1)*Hred(1,1)) % N, "F ≡ GH (mod N) red (1,1)");

\\ evaluation map well-defined: f(m)≡0 so x↦m kills f
check((Mod(13,N)^2 + Mod(13,N) + 5) == Mod(0,N), "eval irr at m is 0 in Z/NZ");
check((Mod(10,N)^2 + 8*Mod(10,N) + 7) == Mod(0,N), "eval red at m is 0 in Z/NZ");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
