\\ Remaining two-form Dirichlet branch: neither leading coeff a
\\ unit, not an inverse pair.  (5,5,24) o (7,7,18) on Delta=-455.
\\ solve_cong is Bezout (extgcd), not Z.ggcd divisors.  Mirrors
\\ compose_neg455_5_7_of_disc.  Completeness forall two-form is
\\ compose_preserves_disc_open_named.  Probe names avoid "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

comp_gcd(f, g) = gcd(gcd(component(f,1), component(g,1)), (component(f,2)+component(g,2))/2);

solve_bezout(a, m, target) = {
  my(d, u, v);
  d = gcd(a, m);
  [u, v] = bezout(a, m);
  u * (target / d)
};

solve_ggcd(a, m, target) = {
  my(d = gcd(a, m));
  (a / d) * (target / d)
};

dirichlet_B(f, g, sol) = {
  my(a1 = component(f,1), a2 = component(g,1));
  my(b1 = component(f,2), b2 = component(g,2));
  my(n, a1p, a2p);
  if(abs(a1)==1, return(b2));
  n = comp_gcd(f, g);
  a1p = a1 / n;
  a2p = a2 / n;
  b1 + 2 * a1p * sol(a1p, a2p, (b2 - b1)/2)
};

our_compose(f, g, sol) = {
  my(n = comp_gcd(f, g));
  my(aa = (component(f,1) * component(g,1)) / (n * n));
  my(B = dirichlet_B(f, g, sol));
  my(D = component(f,2)^2 - 4*component(f,1)*component(f,3));
  Qfb(aa, B, (B*B - D)/(4*aa))
};

disc(f) = component(f,2)^2 - 4*component(f,1)*component(f,3);
prim(f) = gcd(gcd(component(f,1), component(f,2)), component(f,3))==1;

f5 = Qfb(5,5,24);
f7 = Qfb(7,7,18);
id455 = Qfb(1,1,114);
h = our_compose(f5, f7, solve_bezout);

check(disc(f5)==-455,                      "disc (5,5,24) = -455");
check(disc(f7)==-455,                      "disc (7,7,18) = -455");
check(abs(component(f5,1))!=1,             "a(5,5,24) is not a unit");
check(abs(component(f7,1))!=1,             "a(7,7,18) is not a unit");
check(comp_gcd(f5,f7)==1,                  "comp gcd of 5 and 7 is 1");
check(disc(h)==-455,                       "Bezout compose preserves disc");
check(prim(h),                             "Bezout compose is primitive");
check(component(h,1)==35,                  "compose leading coeff is 5*7");
check(qfbred(h)==Qfb(12,11,12),            "reduces to the 13-class");
check(qfbred(f5*f7)==Qfb(12,11,12),        "PARI class agrees");

\\ Z.ggcd divisors are not Bezout: (B^2-D) is not 0 mod 4aa.
Bg = dirichlet_B(f5, f7, solve_ggcd);
aag = (5*7)/(comp_gcd(f5,f7)^2);
Dg = disc(f5);
check((Bg^2 - Dg) % (4*aag) != 0,          "ggcd-quotients do not divide c");

check(our_compose(f5, id455, solve_bezout)==f5, "right id on (5,5,24)");
check(our_compose(id455, f5, solve_bezout)==f5, "left id on (5,5,24)");
check(our_compose(Qfb(3,3,8), Qfb(1,1,22), solve_bezout)==Qfb(3,3,8), "right id on (3,3,8)");

\\ Self-compose of (2,1,4): target 0, Bezout-independent.
f31 = Qfb(2,1,4);
check(our_compose(f31, f31, solve_bezout)==Qfb(4,1,2), "(2,1,4)^2 = (4,1,2)");
check(our_compose(f31, f31, solve_ggcd)==Qfb(4,1,2), "self-compose ignores solver");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
