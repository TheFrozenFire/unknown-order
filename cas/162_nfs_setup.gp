\\ NFS setup identity on the campaign pin (cas/lib/pin.gp).
\\ Mirrors SieveRelation.v hom_quad_remainder / nfs_eval_*.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");
init_pin();

firr(x) = pin_nfs_irr_c2*x^2 + pin_nfs_irr_c1*x + pin_nfs_irr_c0;
fred(x) = pin_nfs_red_c2*x^2 + pin_nfs_red_c1*x + pin_nfs_red_c0;
Firr(a, b) = pin_nfs_irr_c2*a^2 + pin_nfs_irr_c1*a*b + pin_nfs_irr_c0*b^2;
Fred(a, b) = pin_nfs_red_c2*a^2 + pin_nfs_red_c1*a*b + pin_nfs_red_c0*b^2;
Girr(a, b) = a - pin_nfs_irr_m*b;
Hirr(a, b) = pin_nfs_irr_c2*a + (pin_nfs_irr_c2*pin_nfs_irr_m + pin_nfs_irr_c1)*b;
Gred(a, b) = a - pin_nfs_red_m*b;
Hred(a, b) = pin_nfs_red_c2*a + (pin_nfs_red_c2*pin_nfs_red_m + pin_nfs_red_c1)*b;

check(N == p*q,                           "pin N = p q");
check(firr(pin_nfs_irr_m) == N,           "f_irr(m) = N");
check(fred(pin_nfs_red_m) == N,           "f_red(m) = N");
check(firr(pin_nfs_irr_m) % N == 0,       "common root irr");
check(fred(pin_nfs_red_m) % N == 0,       "common root red");
check(issquare(pin_nfs_irr_c1^2 - 4*pin_nfs_irr_c2*pin_nfs_irr_c0) == 0, "irr disc not square");
check(fred(-1) == 0 && fred(-7) == 0,     "f_red splits over Z");

check(Firr(2,1) - firr(pin_nfs_irr_m)*1 == Girr(2,1)*Hirr(2,1), "irr remainder (2,1)");
check(Firr(-5,1) - N == Girr(-5,1)*Hirr(-5,1), "irr remainder (−5,1)");
check(Fred(pin_ts_a1, pin_ts_b1) - N == Gred(pin_ts_a1, pin_ts_b1)*Hred(pin_ts_a1, pin_ts_b1), "red remainder ts1");
check(Fred(pin_ts_a2, pin_ts_b2) - N == Gred(pin_ts_a2, pin_ts_b2)*Hred(pin_ts_a2, pin_ts_b2), "red remainder ts2");
check(Firr(3,2) % N == (Girr(3,2)*Hirr(3,2)) % N, "F ≡ GH irr (3,2)");
check(Fred(1,1) % N == (Gred(1,1)*Hred(1,1)) % N, "F ≡ GH red (1,1)");
check((Mod(pin_nfs_irr_m,N)^2 + Mod(pin_nfs_irr_m,N) + pin_nfs_irr_c0) == Mod(0,N), "eval irr at m is 0");
check((Mod(pin_nfs_red_m,N)^2 + pin_nfs_red_c1*Mod(pin_nfs_red_m,N) + pin_nfs_red_c0) == Mod(0,N), "eval red at m is 0");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
