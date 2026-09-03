\\ Euler converse for cubes when 3 | p-1, via a primitive root.
\\ a is a cube iff a^{(p-1)/3} ≡ 1; every unit is a power of a generator;
\\ cubing is 3-to-1; exactly (p-1)/3 cubes.
\\ Mirrors Order.v primitive_root_generates and CubicResidue.v cube_euler_converse.
\\ Extra modulus p=13, q=7, N=91 is the named cubic instance (cas/86);
\\ pin 11×17=187 has gcd(3,λ)=1 so cubing is a permutation.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

covers(g, p) = {
  okc = 1;
  for(a = 1, p-1,
    found = 0;
    for(k = 0, p-2, if(lift(Mod(g,p)^k) == a, found = 1));
    if(found == 0, okc = 0)
  );
  okc
};

n_cube_roots(a, p) = {
  n = 0;
  for(x = 1, p-1, if(lift(Mod(x,p)^3) == a, n++));
  n
};

is_cube_mod(a, p) = n_cube_roots(a, p) > 0;

euler_one(a, p) = lift(Mod(a,p)^((p-1)/3)) == 1;

cube_euler_iff(p) = {
  okc = 1;
  for(a = 1, p-1,
    if(is_cube_mod(a, p) != euler_one(a, p), okc = 0)
  );
  okc
};

count_cubes(p) = {
  n = 0;
  for(a = 1, p-1, if(euler_one(a, p), n++));
  n
};

three_to_one(p) = {
  okc = 1;
  for(a = 1, p-1,
    if(euler_one(a, p), if(n_cube_roots(a, p) != 3, okc = 0))
  );
  okc
};

perm_cubes(p) = {
  d = lift(1/Mod(3, p-1));
  okc = 1;
  for(a = 1, p-1,
    if(lift(Mod(lift(Mod(a,p)^d), p)^3) != a, okc = 0)
  );
  okc
};

p = 13;
check((p-1) % 3 == 0,                 "3 | 12");
check(znorder(Mod(2,p)) == p-1,       "2 generates F_13*");
check(covers(2, p),                   "every unit of F_13* is a power of 2");
check((p-1)/3 == 4,                   "(p-1)/3 = 4");
check(cube_euler_iff(p),              "a cube iff a^4 ≡ 1 (mod 13)");
check(count_cubes(p) == 4,            "exactly 4 cubes in F_13*");
check(three_to_one(p),                "each cube has 3 roots in F_13*");
check(lift(Mod(2,p)^4) != 1,          "2 is not a cube: 2^4 ≢ 1");
check(lift(Mod(2,p)^4) == 3,          "2^4 ≡ 3, a primitive 3rd root");
check(lift(Mod(3,p)^3) == 1,          "3^3 ≡ 1 (mod 13)");
check(lift(Mod(3,p)^2) == 9,          "3^2 ≡ 9, the other 3rd root");
check(n_cube_roots(1, p) == 3,        "1 has three cube roots");

q = 7;
check((q-1) % 3 == 0,                 "3 | 6");
check(znorder(Mod(3,q)) == q-1,       "3 generates F_7*");
check(covers(3, q),                   "every unit of F_7* is a power of 3");
check(cube_euler_iff(q),              "a cube iff a^2 ≡ 1 (mod 7)");
check(count_cubes(q) == 2,            "exactly 2 cubes in F_7*");

p2 = 11;
check((p2-1) % 3 != 0,                "pin: 3 does not divide 10");
check(perm_cubes(p2),                 "pin: every unit of F_11* is a cube");
check(znorder(Mod(2,p2)) == p2-1,     "2 generates F_11*");
check(covers(2, p2),                  "every unit of F_11* is a power of 2");

check(lcm(10,16) % 3 != 0,            "pin: 3 does not divide λ=80");
check(gcd(3, lcm(10,16)) == 1,        "pin: e=3 is an RSA exponent");
check(lcm(12,6) % 3 == 0,             "91: 3 | λ, e=3 is not RSA");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
