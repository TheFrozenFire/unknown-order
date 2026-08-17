\\ CAS witnesses — CRT constructor for strong/Blum primes.
\\ Mirrors KeyGenCtor.v.  p = a + k M, M = 4 r s,
\\ a ≡ 1 (mod r), a ≡ −1 (mod s), a ≡ 3 (mod 4).

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

r = 3; s = 5; M = 4*r*s;
check(M == 60,                           "M = 4*3*5 = 60");
a = 19;
check(a % r == 1,                        "a ≡ 1 (mod r)");
check(a % s == s-1,                      "a ≡ −1 (mod s)");
check(a % 4 == 3,                        "a ≡ 3 (mod 4)");

p = a + 0*M;
check(isprime(p),                        "p = 19 is prime");
check((p-1) % r == 0,                    "r | p−1");
check((p+1) % s == 0,                    "s | p+1");
check(p % 4 == 3,                        "p is Blum");
B = 2;
check(r > B && s > B,                    "auxiliaries exceed B=2");

\\ next hit in the same slot
p2 = a + 1*M;
check(p2 == 79 && isprime(p2),           "k=1 gives 79, prime");
check((p2-1) % r == 0 && (p2+1) % s == 0 && p2 % 4 == 3, "79 stays in the slot");

\\ second slot: r'=7, s'=3. a ≡ 1 (mod 7), a ≡ −1 (mod 3), a ≡ 3 (mod 4)
a2 = 71;
check(a2 % 7 == 1 && a2 % 3 == 2 && a2 % 4 == 3, "second residue 71");
q = 71;
check(isprime(q),                        "q = 71 is prime");
check((q-1) % 7 == 0 && (q+1) % 3 == 0, "7 | q−1 and 3 | q+1");
\\ 19 and 79 fail balance: placement is a choice of k, not the CRT walk
check(!(19 <= 79 && 79 <= 2*19),         "19,79 not balanced: placement is separate");
check(abs(79-19) >= 2^5,                 "far at gap=5: |79-19|=60");

\\ public-AP discriminator
check(79 % M == a,                       "public AP: 79 ≡ 19 (mod 60)");
check((79 - a) / M == 1,                 "k = 1 is the ROCA unknown");

\\ bits: b=7 (79 < 128), M=60 ≈ 2^5, 2^7/60 + 1 = 3
check(2^7 \ 60 + 1 == 3,                 "AP candidates in [0,128) about 3");

\\ 1024-bit regime knobs
check(512 - 160 == 352,                  "512-bit prime, 160-bit M: 352-bit AP search");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
