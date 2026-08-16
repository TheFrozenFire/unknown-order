\\ CAS witnesses — relation-level hardness structure.
\\ Mirrors Hardness.v.  Winning conditions, not assumptions.
\\ N=187, e=3, d=27, λ=80: the textbook instance.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 11; q = 17; N = p*q; e = 3; d = 27;
lam = lcm(p-1, q-1);

\\ the e-power map is a permutation of the units
units = []; cubes = [];
for(a = 1, N-1, \
  if(gcd(a,N)==1, \
    units = concat(units, [a]); \
    cubes = concat(cubes, [lift(Mod(a,N)^e)]) \
  ) \
);
cubes = vecsort(Set(cubes));
check(#units == eulerphi(N),            "φ(187) units");
check(#cubes == #units,                 "every unit is a cube (permutation)");
check(lift(Mod(42,N)^e)^d % N == 42,    "trapdoor inverts on the test vector");
check(lift(Mod(36,N)^d) == 42,          "36^d = 42");

\\ RSA solution ⇒ strong-RSA solution at that e
check(e > 1 && lift(Mod(42,N)^e) == 36, "Problem_RSA(187,3,36,42)");
check(e > 1 && lift(Mod(42,N)^e) == 36, "hence Problem_StrongRSA(187,36,42,3)");

\\ λ makes strong RSA trivial on every unit: (y, λ+1)
sRSA_fail = 0;
for(i = 1, #units, \
  y = units[i]; \
  if(lift(Mod(y,N)^(lam+1)) != y, sRSA_fail++) \
);
check(sRSA_fail == 0,                   "y^{λ+1} ≡ y for every unit  (lambda_solves_strong_RSA)");

\\ bare relations are inhabited at y=1
check(lift(Mod(1,N)^2) == 1,            "strong RSA trivial at y=1: 1^2 ≡ 1");
check(lift(Mod(1,N)^e) == 1,            "RSA trivial at y=1: 1^e ≡ 1");

\\ order of a unit divides λ
ord2 = znorder(Mod(2,N));
check(lam % ord2 == 0,                  "znorder(2) | λ");
check(lift(Mod(2,N)^ord2) == 1,         "2^{ord} ≡ 1");
check(ord2 > 1,                         "2 is not the identity");

\\ one-sided low order splits; two-sided order does not
check(lift(Mod(2,p)^10) == 1,           "2^{10} ≡ 1 (mod 11)  (p-1 = 10)");
check(lift(Mod(2,q)^10) != 1,           "2^{10} ≢ 1 (mod 17)");
check(gcd(lift(Mod(2,N)^10)-1, N) == p, "one-sided: gcd(2^{10}-1, 187) = 11");
check(lift(Mod(2,N)^ord2) == 1,         "two-sided: 2^{ord} ≡ 1 (mod N), no split");
check(gcd(2^ord2-1, N) == N || gcd(lift(Mod(2,N)^ord2)-1, N) == N, \
                                        "two-sided gcd is N (a^k−1 ≡ 0)");

\\ e not coprime to λ: the map is no longer a permutation
e5 = 5;
check(gcd(e5, lam) == 5,                "5 shares a factor with λ=80");
img5 = [];
for(i = 1, #units, img5 = concat(img5, [lift(Mod(units[i],N)^e5)]));
img5 = vecsort(Set(img5));
check(#img5 < #units,                   "5th-power map on units is not onto");
printf("  [hardness] units=%d  3rd-powers=%d  5th-powers=%d\n", #units, #cubes, #img5);

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
