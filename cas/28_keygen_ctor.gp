\\ CAS witnesses — CRT constructor for strong/Blum/cyclotomic primes.
\\ Mirrors KeyGenCtor.v.  p = a + k M, M = 4 r s u v w,
\\ a ≡ 1 (mod r), a ≡ −1 (mod s), a ≡ 3 (mod 4),
\\ Φ3(a) ≡ 0 (mod u), Φ4(a) ≡ 0 (mod v), Φ6(a) ≡ 0 (mod w).

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

r = 3; s = 5; u = 7; v = 13; w = 19;
M = 4*r*s*u*v*w;
check(M == 103740,                       "M = 4*3*5*7*13*19 = 103740");

a = 13099;
check(a % r == 1,                        "a ≡ 1 (mod r)");
check(a % s == s-1,                      "a ≡ −1 (mod s)");
check(a % 4 == 3,                        "a ≡ 3 (mod 4)");
check((a*a + a + 1) % u == 0,            "u | Φ3(a)");
check((a*a + 1) % v == 0,                "v | Φ4(a)");
check((a*a - a + 1) % w == 0,            "w | Φ6(a)");

p = a + 0*M;
check(isprime(p),                        "p = 13099 is prime");
check((p-1) % r == 0,                    "r | p−1");
check((p+1) % s == 0,                    "s | p+1");
check(p % 4 == 3,                        "p is Blum");
check((p*p + p + 1) % u == 0,            "u | Φ3(p)");
check((p*p + 1) % v == 0,                "v | Φ4(p)");
check((p*p - p + 1) % w == 0,            "w | Φ6(p)");
B = 2;
check(r > B && s > B && u > B && v > B && w > B, "auxiliaries exceed B=2");

\\ next hit in the same slot
p2 = a + 2*M;
check(p2 == 220579 && isprime(p2),       "k=2 gives 220579, prime");
check((p2-1) % r == 0 && (p2+1) % s == 0 && p2 % 4 == 3, "220579 stays Blum / p±1");
check((p2*p2 + p2 + 1) % u == 0 && (p2*p2 + 1) % v == 0 && (p2*p2 - p2 + 1) % w == 0, "220579 stays in Φ3/Φ4/Φ6");

\\ second slot: r'=5, s'=3, same (u,v,w). Residue 21611 is itself prime.
a2 = 21611;
check(a2 % 5 == 1 && a2 % 3 == 2 && a2 % 4 == 3, "second residue 21611 on r,s,4");
check((a2*a2 + a2 + 1) % u == 0 && (a2*a2 + 1) % v == 0 && (a2*a2 - a2 + 1) % w == 0, "21611 on Φ3/Φ4/Φ6");
q = 21611;
check(isprime(q),                        "q = 21611 is prime");
check((q-1) % 5 == 0 && (q+1) % 3 == 0, "5 | q−1 and 3 | q+1");

\\ same-slot 13099 and 220579 fail balance: placement is a choice of k
check(!(13099 <= 220579 && 220579 <= 2*13099), "13099,220579 not balanced: placement is separate");
check(13099 <= 21611 && 21611 <= 2*13099, "cross-slot 13099,21611 is balanced");
check(abs(21611-13099) >= 2^13,          "far at gap=13: |21611-13099|=8512");

\\ public-AP discriminator
check(220579 % M == a,                   "public AP: 220579 ≡ 13099 (mod 103740)");
check((220579 - a) / M == 2,             "k = 2 is the ROCA unknown");

\\ bits: b=18 (220579 < 2^18), M=103740 ≈ 2^17, 2^18/M + 1 = 3
check(2^18 \ 103740 + 1 == 3,            "AP candidates in [0,2^18) about 3");

\\ 1024-bit regime knobs
check(512 - 160 == 352,                  "512-bit prime, 160-bit M: 352-bit AP search");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
