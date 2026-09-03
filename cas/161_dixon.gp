\\ Dixon / QS combination on the campaign pin (cas/lib/pin.gp).
\\ Mirrors SieveRelation.v dixon_two_relations / dixon_pin_splits.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");
init_pin();

check(N == p*q,                           "pin N = p q");
check((pin_dixon_a^2) % N == pin_dixon_r, "dixon a^2 ≡ r (mod N)");
check((pin_dixon_b^2) % N == pin_dixon_s, "dixon b^2 ≡ s (mod N)");
check(pin_dixon_r * pin_dixon_s == pin_dixon_t^2, "r s = t^2");
check((pin_dixon_a*pin_dixon_b)^2 % N == pin_dixon_t^2 % N, "(a b)^2 ≡ t^2");
check((pin_dixon_a*pin_dixon_b) % N != pin_dixon_t % N, "ab ≢ t");
check((pin_dixon_a*pin_dixon_b) % N != (N-pin_dixon_t) % N, "ab ≢ −t");
check(gcd(pin_dixon_a*pin_dixon_b - pin_dixon_t, N) == p, "gcd(ab−t, N) = p");
check(gcd(pin_dixon_a*pin_dixon_b + pin_dixon_t, N) == q, "gcd(ab+t, N) = q");

check((pin_asquare_a^2) % N == pin_asquare_t^2 % N, "already-square a^2 ≡ t^2");
check(gcd(pin_asquare_a - pin_asquare_t, N) == p, "length-1 gcd = p");

check((pin_dixon_b2^2) % N == pin_dixon_s2, "second combo b2^2 ≡ s2");
check(pin_dixon_r * pin_dixon_s2 == pin_dixon_t2^2, "r s2 = t2^2");
check(gcd(pin_dixon_a*pin_dixon_b2 - pin_dixon_t2, N) == q, "second combo splits q");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
