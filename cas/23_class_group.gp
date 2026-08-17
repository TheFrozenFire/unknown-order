\\ CAS witnesses — Cl(Δ) for imaginary quadratic discriminants.
\\ Mirrors BinForms.v: reduced forms, public order-2 classes from
\\ factors of Δ, 2-rank vs ω(Δ), no odd annihilator from Δ itself.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

idform(D) = qfbred(Qfb(1, D%2, (D%2 - D)/4));

reduced_forms(D) = {
  my(forms = List(), bmax, ac, c);
  bmax = sqrtint((-D)\3);
  for(b = -bmax, bmax, \
    if((b^2 - D) % 4 == 0, \
      ac = (b^2 - D)/4; \
      fordiv(ac, a, \
        c = ac/a; \
        if(abs(b) <= a && a <= c && (b >= 0 || (a != abs(b) && a != c)), \
          listput(forms, Qfb(a,b,c)) \
        ) \
      ) \
    ) \
  );
  Vec(forms)
};

form_order(f, D) = {
  my(id = idform(D), g = qfbred(f), n = 1);
  while(g != id && n < 200, g = qfbred(g*f); n++);
  n
};

is_amb_red(f) = {
  my(a = component(f,1), b = component(f,2), c = component(f,3));
  b == 0 || a == b || a == -b || a == c
};

omega_odd(D) = {
  my(F = factor(abs(D)), t = 0);
  for(i = 1, matsize(F)[1], if(F[i,1] % 2 == 1, t++));
  t
};

catalog = [-23, -47, -87, -403, -455];

for(di = 1, length(catalog), \
  D = catalog[di]; \
  check(D < 0 && (D%4==0 || D%4==1), Str("iq disc ", D)); \
  forms = reduced_forms(D); \
  h = length(forms); \
  check(h == qfbclassno(D), Str("reduced count = h(", D, ") = ", h)); \
  id = idform(D); \
  check(form_order(id, D) == 1, Str("identity has order 1 on ", D)); \
  n2 = 0; has_odd = 0; oddn = 0; \
  for(i = 1, h, \
    f = forms[i]; \
    n = form_order(f, D); \
    if(n == 2, n2++); \
    if(n % 2 == 1 && n > 1, has_odd = 1; oddn = n); \
    if(n == 2, check(is_amb_red(f), Str("order-2 reduced form is ambiguous on ", D))) \
  ); \
  t = omega_odd(D); \
  expect2 = 2^(t-1) - 1; \
  check(n2 == expect2, Str("2-rank on ", D, ": ", n2, " non-id order-2, expect ", expect2)); \
  if(has_odd, check(oddn != abs(D), Str("odd order on ", D, " is not |D|"))); \
  killed_by_D = 1; \
  for(i = 1, h, \
    f = forms[i]; \
    if(qfbred(f^D) != id, killed_by_D = 0) \
  ); \
  check(!killed_by_D || h==1, Str("odd D does not annihilate Cl(", D, ")")); \
  if(h == 2, \
    check((D+1)%2==0 && qfbred(forms[2]^(D+1))==id, \
      Str("h=2: D+1 annihilates ", D, " only because it is even")) \
  ) \
);

check(qfbred(Qfb(3,3,8)) == Qfb(3,3,8),           "(-87) (3,3,8) reduced");
check(form_order(Qfb(3,3,8), -87) == 2,            "(-87) (3,3,8) has order 2");
check(qfbred(Qfb(13,13,11)) == Qfb(11,9,11),       "(-403) (13,13,11) ~ (11,9,11)");
check(form_order(Qfb(11,9,11), -403) == 2,         "(-403) (11,9,11) has order 2");
check(form_order(Qfb(5,5,24), -455) == 2,          "(-455) (5,5,24) has order 2");
check(form_order(Qfb(7,7,18), -455) == 2,          "(-455) (7,7,18) has order 2");
check(qfbred(Qfb(13,13,12)) == Qfb(12,11,12),      "(-455) (13,13,12) ~ (12,11,12)");
check(form_order(Qfb(12,11,12), -455) == 2,        "(-455) (12,11,12) has order 2");

check(idform(-87)*Qfb(3,3,8) == Qfb(3,3,8),        "id compose (3,3,8) = (3,3,8)");
check(qfbred(Qfb(3,3,8)*Qfb(3,-3,8)) == idform(-87), "(3,3,8) compose inverse ~ id");

check(qfbclassno(-23) == 3,                        "h(-23)=3");
check(qfbclassno(-47) == 5,                        "h(-47)=5");
forms23 = reduced_forms(-23);
n2_23 = 0;
for(i = 1, length(forms23), if(form_order(forms23[i],-23)==2, n2_23++));
check(n2_23 == 0,                                  "Cl(-23) has no order-2");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
