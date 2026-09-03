\\ Cubic character a^{(p-1)/3} takes values in mu_3; kernel of cubing
\\ is {1, omega, omega^2} locally and CRT of those pairs on N=pq.
\\ Mirrors CubicResidue.v omega_from_primitive_root / cube_kernel_* /
\\ pin_cube_kernel_trivial. Named extra 13×7=91 (cas/86); pin 187
\\ has trivial kernel because gcd(3,λ)=1.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

n_mu3(m) = {
  my(c = 0, x);
  for(x = 1, m-1, if(gcd(x,m)==1 && lift(Mod(x,m)^3)==1, c++));
  c
};

char_in_mu3(p, om) = {
  my(okc = 1, a, chi);
  for(a = 1, p-1,
    chi = lift(Mod(a,p)^((p-1)/3));
    if(chi != 1 && chi != om && chi != lift(Mod(om,p)^2), okc = 0)
  );
  okc
};

char_mul(p) = {
  my(okc = 1, a, b, lhs, rhs);
  for(a = 1, p-1,
    for(b = 1, p-1,
      lhs = lift(Mod(a*b, p)^((p-1)/3));
      rhs = lift(Mod(lift(Mod(a,p)^((p-1)/3)) * lift(Mod(b,p)^((p-1)/3)), p));
      if(lhs != rhs, okc = 0)
    )
  );
  okc
};

p = pin_91_p;
g = 2;
om = lift(Mod(g,p)^((p-1)/3));
check(znorder(Mod(g,p)) == p-1,           "2 generates F_13*");
check(om == 3,                            "omega = 2^4 ≡ 3 (mod 13)");
check(znorder(Mod(om,p)) == 3,            "omega has order 3");
check(lift(Mod(om,p)^2) == 9,             "omega^2 ≡ 9");
check(n_mu3(p) == 3,                      "3 solutions of x^3=1 in F_13*");
check(lift(Mod(1,p)^3)==1,                "1^3=1");
check(lift(Mod(3,p)^3)==1,                "3^3=1");
check(lift(Mod(9,p)^3)==1,                "9^3=1");
check((3*3+3+1) % 13 == 0,                "omega^2+omega+1=0 mod 13");
check(char_in_mu3(p, om),                 "cube_char takes values in {1,3,9}");
check(char_mul(p),                        "cube_char is multiplicative");
check(lift(Mod(8,p)^4)==1,                "cube 8 has character 1");
check(lift(Mod(2,p)^4)==3,                "non-cube 2 has character omega");

q = pin_91_q;
omq = lift(Mod(3,q)^((q-1)/3));
check(znorder(Mod(3,q)) == q-1,           "3 generates F_7*");
check(omq == 2,                           "omega_7 = 3^2 ≡ 2");
check(n_mu3(q) == 3,                      "3 solutions of x^3=1 in F_7*");
check(lift(Mod(1,q)^3)==1,                "1^3=1 mod 7");
check(lift(Mod(2,q)^3)==1,                "2^3=1 mod 7");
check(lift(Mod(4,q)^3)==1,                "4^3=1 mod 7");

N = pin_91;
check(n_mu3(N) == 9,                      "9 solutions of x^3=1 in (Z/91Z)*");
x_mixed = lift(chinese(Mod(3,13), Mod(1,7)));
check(x_mixed % 13 == 3,                  "CRT(omega_13, 1) ≡ 3 (mod 13)");
check(x_mixed % 7 == 1,                   "CRT(omega_13, 1) ≡ 1 (mod 7)");
check(gcd(x_mixed, N)==1,                 "mixed kernel element is a unit");
check(lift(Mod(x_mixed,N)^3)==1,          "mixed kernel: x^3≡1 (mod 91)");
check(x_mixed != 1,                       "mixed kernel element is not 1");

Npin = pin_N;
check(gcd(3, lcm(10,16))==1,              "pin: gcd(3,λ)=1");
check(n_mu3(Npin) == 1,                   "pin: only unit with x^3≡1 is 1");
check(lift(Mod(1,Npin)^3)==1,             "pin: 1^3=1");
check(lift(Mod(186,Npin)^3) != 1,         "pin: (-1)^3 ≢ 1");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
