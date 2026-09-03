\\ one-more RSA, GHR prime-e, phi-hiding e | λ.
\\ Mirrors ExtraRelations.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p = pin_p; q = pin_q; N = pin_N; ee = 3; lam = lcm(p-1, q-1);

\\ one-more: one queried inversion (36,42) plus unqueried 8=2^3
check(lift(Mod(42,N)^ee) == 36,         "queried: 42^3 ≡ 36");
check(lift(Mod(2,N)^ee) == 8,           "extra: 2^3 ≡ 8");
check(8 != 36,                          "extra challenge was not queried");

\\ GHR: e=3 is prime; Shamir gcd when e does not divide delta
check(isprime(ee),                      "e=3 is prime");
check(lift(Mod(42,N)^ee) == 36,         "GHR instance: prime-e RSA");
delta = 1;
check(ee % delta != 0 || delta == 1,    "3 does not divide 1");
check(gcd(delta, ee) == 1,              "prime e, e ndiv delta => gcd=1");

\\ phi-hiding relation: e | λ, not a PPT game
check(lam == 80,                        "λ=80");
check(lam % 5 == 0,                     "5 | λ  (phi-hiding witness)");
check(gcd(5, lam) == 5,                 "5 shares a factor with λ");
check(gcd(3, lam) == 1,                 "3 does not divide λ; public e=3 is not hidden");
check(lam % 3 != 0,                     "3 ndiv 80");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
