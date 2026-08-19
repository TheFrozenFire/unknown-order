\\ Cubic residuosity when 3 | p-1.  Mirrors CubicResidue.v.
\\ p=13 (3|12), q=7 (3|6), N=91, lambda=12, 3|lambda so e=3 is not RSA.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 13; q = 7; N = p*q;
check((p-1) % 3 == 0, "3 | p-1");
check((q-1) % 3 == 0, "3 | q-1");
lam = lcm(p-1, q-1);
check(lam % 3 == 0, "3 | lambda: e=3 is not an RSA exponent");
check(gcd(3, lam) == 3, "gcd(3, lambda) != 1");

\\ cubes mod p: a^{(p-1)/3} == 1
cube_ok = 1; ncubes = 0;
for(x = 1, p-1, \
  a = lift(Mod(x,p)^3); \
  ncubes++; \
  if(lift(Mod(a,p)^((p-1)/3)) != 1, cube_ok = 0) \
);
check(cube_ok, "every cube satisfies a^{(p-1)/3}=1 mod p");

\\ when gcd(3,p-1)=1 cubing is a permutation (p=11)
p2 = 11;
check((p2-1) % 3 != 0, "11: 3 does not divide p-1");
d = lift(1/Mod(3, p2-1));
perm_ok = 1;
for(a = 1, p2-1, \
  root = lift(Mod(a,p2)^d); \
  if(lift(Mod(root,p2)^3) != a, perm_ok = 0) \
);
check(perm_ok, "gcd(3,10)=1 => a |-> a^d is a cube-root map");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
