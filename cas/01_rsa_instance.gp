\\ CAS witnesses — RSA instance, private exponent d, encrypt/decrypt.
\\ Mirrors unknown-order/rocq/RSA.v (rsa_test: p=11, q=17, e=3, d=27).
\\ Ground truth: N = pin_N, λ = lcm(10,16) = 80, 3*27 = 81 ≡ 1 (mod 80).
\\ d is the inverse of e modulo λ, not "a cube root".  Exponentiation
\\ by d *is* the cube-root map on units.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p = pin_p; q = pin_q; N = pin_N; e = pin_e; d = pin_d;
lam = lcm(p-1, q-1);
phi = (p-1)*(q-1);

check(N == pin_p*pin_q,                 "N = pin_p pin_q");
check(lam == 80,                        "λ(N) = lcm(10,16) = 80");
check(phi == 160,                       "φ(N) = 10*16 = 160");
check((e*d) % lam == 1,                 "e*d ≡ 1 (mod λ)");
check(gcd(e, lam) == 1,                 "e coprime to λ");
check(lam % (p-1) == 0 && lam % (q-1) == 0, "λ is a common multiple of p-1, q-1");
check(phi % lam == 0,                   "λ | φ");

\\ encryption / decryption on the Rocq test vector
m = 42;
c = lift(Mod(m, N)^e);
m2 = lift(Mod(c, N)^d);
check(c == 36,                          "enc(42) = 36  (rsa_test_vector)");
check(m2 == 42,                         "dec(36) = 42");
check(lift(Mod(c, N)^d) == m,           "round-trip on the test vector");

\\ cube-root reading: for e=3, raising to d extracts a cube root
check(lift(Mod(m, N)^3) == c,           "42^3 ≡ 36 (mod 187) — cubing");
check(lift(Mod(c, N)^d) == m,           "36^d ≡ 42 — d realises the cube-root map");

\\ random units: dec ∘ enc = id
setrand(1);
rt_fail = 0;
for(t = 1, 200, \
  a = 1 + random(N-2); \
  if(gcd(a,N)==1 && lift(Mod(lift(Mod(a,N)^e),N)^d) != a % N, rt_fail++) \
);
check(rt_fail == 0,                     "round-trip on 200 random units");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
