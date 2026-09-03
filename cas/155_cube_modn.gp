\\ Cubic residuosity of N=pq is CRT of local cubes.
\\ a^{λ/3}≡1 is necessary when 3|λ, not sufficient (Jacobi analogue).
\\ Mirrors CubicResidue.v cube_N_iff_both / cube_euler_lambda_*.
\\ Named extras: 13×7=91 (cas/86 cubic instance), 13×19=247 (matching orders).
\\ Pin 11×17=187: gcd(3,λ)=1 so every unit is a cube.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

n_cube_roots(a, m) = {
  my(c = 0);
  for(x = 1, m-1, if(gcd(x,m)==1 && lift(Mod(x,m)^3)==a, c++));
  c
};

is_cube(a, m) = n_cube_roots(a, m) > 0;

crt_cubes(p, q) = {
  my(N = p*q, okc = 1, a, loc, glob);
  for(a = 1, N-1,
    if(gcd(a,N)==1,
      loc = is_cube(a%p, p) && is_cube(a%q, q);
      glob = is_cube(a, N);
      if(glob != loc, okc = 0)
    )
  );
  okc
};

count_cubes(N) = {
  my(c = 0, a);
  for(a = 1, N-1, if(gcd(a,N)==1 && is_cube(a, N), c++));
  c
};

count_euler(N, e) = {
  my(c = 0, a);
  for(a = 1, N-1, if(gcd(a,N)==1 && lift(Mod(a,N)^e)==1, c++));
  c
};

count_units(N) = {
  my(c = 0, a);
  for(a = 1, N-1, if(gcd(a,N)==1, c++));
  c
};

all_units_cubes(N) = {
  my(okc = 1, a);
  for(a = 1, N-1,
    if(gcd(a,N)==1, if(!is_cube(a, N), okc = 0))
  );
  okc
};

p = pin_91_p; q = pin_91_q; N = pin_91; lam = pin_91_lam;
check(N == pin_91,                          "named extra pin_91");
check(lam == 12,                          "λ(91)=12");
check(lam % 3 == 0,                       "3 | λ(91)");

check(is_cube(1, N),                      "1 is a cube mod 91");
check(is_cube(8, N),                      "8 is a cube mod 91");
check(is_cube(8%p, p) && is_cube(8%q, q), "8 is a cube locally");
check(n_cube_roots(1, N) == 9,            "9 cube roots of 1 in (Z/91Z)*");
check(n_cube_roots(8, N) == 9,            "each cube has 9 unit roots");

check(is_cube(5%p, p),                    "5 is a cube mod 13");
check(!is_cube(5%q, q),                   "5 is not a cube mod 7");
check(!is_cube(5, N),                     "mixed: 5 is not a cube mod 91");
check(is_cube(6%q, q),                    "6 is a cube mod 7");
check(!is_cube(6%p, p),                   "6 is not a cube mod 13");
check(!is_cube(6, N),                     "mixed: 6 is not a cube mod 91");

check(crt_cubes(p, q),                    "91: cube mod N iff both locals");
check(count_units(N) == 72,               "φ(91)=72");
check(count_cubes(N) == 8,                "exactly φ/9=8 cubes");
check(count_euler(N, lam/3) == 8,         "on 91, a^{λ/3}≡1 matches cubes");

p2 = pin_247_p; q2 = pin_247_q; N2 = pin_247; lam2 = pin_247_lam;
check(N2 == pin_247,                        "named extra pin_247");
check(lam2 == 36,                         "λ(247)=36");
check(lam2 % 3 == 0,                      "3 | λ(247)");
check(gcd(7, N2)==1,                      "7 is a unit of Z/247Z");
check(lift(Mod(7,N2)^(lam2/3))==1,        "7^{12} ≡ 1 (mod 247)");
check(!is_cube(7%p2, p2),                 "7 is not a cube mod 13");
check(is_cube(7%q2, q2),                  "7 is a cube mod 19");
check(!is_cube(7, N2),                    "7^{12}≡1 but 7 is not a cube mod 247");

p3 = 11; q3 = 17; N3 = p3*q3; lam3 = lcm(10,16);
check(gcd(3, lam3)==1,                    "pin: gcd(3,λ)=1");
check(all_units_cubes(N3),                "pin: every unit of Z/187Z is a cube");
check(count_units(N3) == 160,             "pin: φ(187)=160");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
