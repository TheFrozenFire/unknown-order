\\ Dirichlet assoc remaining cases.  {id,f,f^{-1}} is
\\ compose_assoc_id_inv.  This file: {id,f,f} and the order-3
\\ pin (f o f) o f = f o (f o f) on Delta=-31, form (2,1,4).
\\ Forall triples is compose_assoc_open_named.  Mirrors
\\ compose_assoc_id_ff / compose_assoc_neg31_ord3.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

comp_gcd(f, g) = gcd(gcd(component(f,1), component(g,1)), (component(f,2)+component(g,2))/2);

solve_bezout(a, m, target) = {
  my(d, u, v);
  d = gcd(a, m);
  [u, v] = bezout(a, m);
  u * (target / d)
};

dirichlet_B(f, g) = {
  my(a1 = component(f,1), a2 = component(g,1));
  my(b1 = component(f,2), b2 = component(g,2));
  my(n, a1p, a2p);
  if(abs(a1)==1, return(b2));
  n = comp_gcd(f, g);
  a1p = a1 / n;
  a2p = a2 / n;
  b1 + 2 * a1p * solve_bezout(a1p, a2p, (b2 - b1)/2)
};

our_compose(f, g) = {
  my(n = comp_gcd(f, g));
  my(aa = (component(f,1) * component(g,1)) / (n * n));
  my(B = dirichlet_B(f, g));
  my(D = component(f,2)^2 - 4*component(f,1)*component(f,3));
  Qfb(aa, B, (B*B - D)/(4*aa))
};

disc(f) = component(f,2)^2 - 4*component(f,1)*component(f,3);

f = Qfb(2,1,4);
id31 = Qfb(1,1,8);
sq = our_compose(f, f);
lft = our_compose(sq, f);
rgt = our_compose(f, sq);

check(disc(f)==-31,                         "disc (2,1,4) = -31");
check(sq==Qfb(4,1,2),                       "(2,1,4)^2 = (4,1,2)");
check(lft==Qfb(8,1,1),                      "((2,1,4)^2) o (2,1,4) = (8,1,1)");
check(rgt==Qfb(8,1,1),                      "(2,1,4) o ((2,1,4)^2) = (8,1,1)");
check(lft==rgt,                             "assoc pin on order-3 form");
check(disc(lft)==-31,                       "triple compose preserves disc");
check(qfbred(lft)==id31,                    "unreduced cube reduces to id");
check(qfbred((f*f)*f)==qfbred(f*(f*f)),     "PARI assoc on the class");

idf = our_compose(id31, f);
check(idf==f,                               "id o f = f");
check(our_compose(idf, f)==sq,              "(id o f) o f = f o f");
check(our_compose(id31, sq)==sq,            "id o (f o f) = f o f");
check(our_compose(idf, f)==our_compose(id31, sq), "{id,f,f} assoc");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
