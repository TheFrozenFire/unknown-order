\\ CAS witnesses — small public e: the RSA map is a low-degree polynomial.
\\ Mirrors SmallExponent.v.  Hastad: same m, e=3, three coprime moduli,
\\ m^3 < N1 N2 N3 ⇒ CRT lift IS m^3 in Z.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

m = 42; cube = m*m*m;
check(cube == 74088,                    "42^3 = 74088");

N1 = 11*17; N2 = 13*19; N3 = 23*29;
check(N1 == 187 && N2 == 247 && N3 == 667, "three textbook moduli");
check(gcd(N1,N2)==1 && gcd(N1,N3)==1 && gcd(N2,N3)==1, "pairwise coprime");

c1 = lift(Mod(m, N1)^3);
c2 = lift(Mod(m, N2)^3);
c3 = lift(Mod(m, N3)^3);
check(c1 == cube % N1,                  "c1 ≡ m^3 (mod N1)");
check(c2 == cube % N2,                  "c2 ≡ m^3 (mod N2)");
check(c3 == cube % N3,                  "c3 ≡ m^3 (mod N3)");

M = N1*N2*N3;
check(cube < M,                         "m^3 < N1 N2 N3");

\\ CRT lift of (c1,c2,c3)
c = lift(chinese(Mod(c1,N1), chinese(Mod(c2,N2), Mod(c3,N3))));
if(c < 0, c = c + M);
check(c == cube,                        "CRT lift of the three ciphertexts is m^3");
check(sqrtn(c, 3) == m,                 "integer cube root recovers m");

\\ related-message shape (Franklin-Reiter): known offset
delta = 5; m2 = m + delta;
cA = lift(Mod(m, N1)^3);
cB = lift(Mod(m2, N1)^3);
check(cB - cA == lift(Mod(m2,N1)^3) - lift(Mod(m,N1)^3), "related ciphertexts");
\\ (m+d)^3 - m^3 = 3 m^2 d + 3 m d^2 + d^3
rel = 3*m*m*delta + 3*m*delta*delta + delta*delta*delta;
check((cB - cA - rel) % N1 == 0,        "known-delta polynomial relation holds");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
