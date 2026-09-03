\\ Two-sided combination on the campaign pin (cas/lib/pin.gp).
\\ Mirrors SieveRelation.v nfs_two_sided_product / nfs_two_sided_splits.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");
init_pin();

Fred(a, b) = pin_nfs_red_c2*a^2 + pin_nfs_red_c1*a*b + pin_nfs_red_c0*b^2;
Gred(a, b) = a - pin_nfs_red_m*b;
Hred(a, b) = pin_nfs_red_c2*a + (pin_nfs_red_c2*pin_nfs_red_m + pin_nfs_red_c1)*b;

G1 = Gred(pin_ts_a1, pin_ts_b1); H1 = Hred(pin_ts_a1, pin_ts_b1); F1 = Fred(pin_ts_a1, pin_ts_b1);
G2 = Gred(pin_ts_a2, pin_ts_b2); H2 = Hred(pin_ts_a2, pin_ts_b2); F2 = Fred(pin_ts_a2, pin_ts_b2);

check(N == p*q,                           "pin N = p q");
check(F1 == G1*H1 + N*pin_ts_b1^2,        "F1 = G1 H1 + N b1^2");
check(F2 == G2*H2 + N*pin_ts_b2^2,        "F2 = G2 H2 + N b2^2");
check(G1*G2 == pin_ts_T^2,                "Π G = T^2");
check(H1*H2 == pin_ts_U^2,                "Π H = U^2");
check((F1*F2) % N == (pin_ts_T*pin_ts_U)^2 % N, "Π F ≡ (T U)^2");
check((pin_ts_T*pin_ts_U)^2 % N == pin_ts_y % N, "(T U)^2 ≡ y");
check((pin_ts_T*pin_ts_U) % N != pin_ts_y % N, "TU ≢ y");
check((pin_ts_T*pin_ts_U) % N != (N-pin_ts_y) % N, "TU ≢ −y");
check(gcd(pin_ts_T*pin_ts_U - pin_ts_y, N) == q, "gcd(TU−y, N) = q");
check(gcd(pin_ts_T*pin_ts_U + pin_ts_y, N) == p, "gcd(TU+y, N) = p");

check(Gred(pin_os_a, pin_os_b) == -pin_os_gs^2, "onesided G = −gs^2");
check(Fred(pin_os_a, pin_os_b) == pin_os_fs^2, "onesided F = fs^2");
check(gcd(pin_os_fs - pin_os_gs, N) == 1, "onesided leftover does not split");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
