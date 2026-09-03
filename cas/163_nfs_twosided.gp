\\ Two-sided combination: G-product and H-product both squares ⇒
\\ F-product ≡ square (mod N) via F ≡ GH, then gcd splits.
\\ Pin: f=x^2+8x+7, m=10, relations (−15,1) and (−6,1).
\\ Π G = 400 = 20^2, Π H = 36 = 6^2, Π F ≡ 1, (20·6)^2 ≡ 1,
\\ gcd(120−1,187)=17.  f is reducible over Z; the combination
\\ identity does not use a field (cas/162 pins the irreducible
\\ companion).  Mirrors SieveRelation.v nfs_two_sided_* .

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

N = 11*17;
Fred(a, b) = a^2 + 8*a*b + 7*b^2;
Gred(a, b) = a - 10*b;
Hred(a, b) = a + 18*b;

a1 = -15; b1 = 1; a2 = -6; b2 = 1;
G1 = Gred(a1, b1); H1 = Hred(a1, b1); F1 = Fred(a1, b1);
G2 = Gred(a2, b2); H2 = Hred(a2, b2); F2 = Fred(a2, b2);

check(G1 == -25 && H1 == 3 && F1 == 112,  "relation (−15,1)");
check(G2 == -16 && H2 == 12 && F2 == -5,  "relation (−6,1)");
check(F1 == G1*H1 + N*b1^2,               "F1 = G1 H1 + N b1^2");
check(F2 == G2*H2 + N*b2^2,               "F2 = G2 H2 + N b2^2");
check(G1*G2 == 20^2,                      "Π G = 20^2");
check(H1*H2 == 6^2,                       "Π H = 6^2");
check((F1*F2) % N == 1,                   "Π F ≡ 1 (mod N)");
check(((G1*G2)*(H1*H2)) % N == 1,         "Π G Π H ≡ 1");
check((20*6)^2 % N == 1,                  "(20·6)^2 ≡ 1");
check(120 % N != 1 && 120 % N != N-1,     "120 ≢ ±1");
check(gcd(120-1, N) == 17,                "gcd(119,187)=17");
check(gcd(120+1, N) == 11,                "gcd(121,187)=11");

\\ contrast: a single already-square pair does not need combination
check(Gred(1,1) == -9 && Fred(1,1) == 16, "(1,1): G=−3^2, F=4^2");
check(Hred(1,1) == 19,                    "H=19 not a square: one-sided leftover");
check(gcd(4-3, N) == 1,                   "Fsqrt vs |G|sqrt does not split");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
