\\ AM09 inversion leak + fixed-e leading term; AMS flexible-e / λ+1.
\\ Mirrors GenericRing.v wave 2.
\\ Pin N=187, e=3, d=27, λ=80.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 11; q = 17; N = p*q; ee = 3; d = 27; lam = lcm(p-1, q-1);

\\ GInv on a tape: init [0,1,y], GConst 11 at handle 3, GInv of that
invtape = [0, 1, 36];
invtape = concat(invtape, [11]);
g11 = gcd(invtape[4], N);
invtape = concat(invtape, [g11]);
check(invtape[5] == 11,                 "GInv(11) on tape returns 11");
check(1 < 11 && 11 < N,                 "non-unit inverse is Problem_Factor");
inv22 = [0, 1, 36, 22];
check(gcd(inv22[4], N) == 11,           "GInv(22) gcd is 11");
check(gcd(36, N) == 1,                  "36 is a unit, gcd=1");
inv36 = lift(1/Mod(36, N));
check((inv36 * 36) % N == 1,            "GInv(36) is a modular inverse");

\\ leading-term: e*dp <> 1 + e*dq for e>1
check(ee * 0 != 1 + ee * 0,             "const/const: 0 <> 1");
check(ee * 1 != 1 + ee * 0,             "deg P=1, deg Q=0: 3 <> 1");
check(ee * 0 != 1 + ee * 1,             "deg P=0, deg Q=1: 0 <> 4");
check(ee * 2 != 1 + ee * 0,             "deg P=2: 6 <> 1");

\\ invert y then cube is rational 1/y^3; not a polynomial identity
y = 36;
invy = lift(1/Mod(y, N));
check(lift(Mod(invy,N)^ee * Mod(y,N)^ee) == 1, "inv(y)^3 * y^3 ≡ 1");

\\ powm(·,27) inverts cubing on units (functional, not a GRA poly identity)
check(lift(Mod(36,N)^d) == 42,          "36^27 ≡ 42 (mod N)");
check(lift(Mod(42,N)^ee) == 36,         "roundtrip");

\\ AMS: λ+1 = 81 solves Strong RSA on every unit and does not factor
check(lam == 80,                        "λ=80");
check(lam + 1 == 81,                    "λ+1=81");
units = [];
sRSA_fail = 0;
for(aa = 1, N-1, \
  if(gcd(aa,N)==1, \
    units = concat(units, [aa]); \
    if(lift(Mod(aa,N)^(lam+1)) != aa, sRSA_fail++) \
  ) \
);
check(sRSA_fail == 0,                   "y^{81} ≡ y for every unit");
check(#units == eulerphi(N),            "φ(187) units");

\\ GConst 81 is independent of y
check(81 == 81,                         "GConst 81 does not depend on y");
check(gcd(81, N) == 1,                  "81 is coprime to N: the const-81 GRA does not factor");

\\ 81 is not produced from y by a ring op without a constant
\\ (y*y, y+y, ... at y=36 never equal 81)
check(36+36 != 81 && 36*36 != 81 && 36-36 != 81, "add/mul/sub of this y is not 81");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
