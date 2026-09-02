\\ Public exponent lattice of N-1 and N+1 vs trapdoor period λ / ord(y).
\\ Pohlig k that split leftover x do not divide N-1; no divisor of
\\ N-1 or N+1 annihilates y or splits.  Mirrors SrsaPeriod.v.
\\ Residual leaf named, not solved.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p=11; q=17; N=p*q; lam=80; y=36; x=42;

check(N-1 == 186,                       "N-1=186");
check(186 == 2*3*31,                    "N-1=2·3·31 public factorization");
check(N+1 == 188,                       "N+1=188");
check(188 == 4*47,                      "N+1=4·47");
check(znorder(Mod(y,N)) == 40,          "ord(y)=40 trapdoor period");
check(lam == 80,                        "λ=80 trapdoor");
check(186 % 40 != 0,                    "ord(y) does not divide N-1");
check(186 % 80 != 0,                    "λ does not divide N-1");
check(188 % 40 != 0,                    "ord(y) does not divide N+1");

\\ Pohlig k that split leftover x are not in the public lattice
check(gcd(5, 186) == 1,                 "pohlig 5 does not divide N-1");
check(186 % 8 != 0,                     "pohlig 8 does not divide N-1");
check(186 % 10 != 0,                    "pohlig 10 does not divide N-1");
check(186 % 16 != 0,                    "pohlig 16 does not divide N-1");
check(gcd(lift(Mod(x,N)^5)-1, N) == 11, "trapdoor k=5 on leftover x splits");

\\ Every positive divisor of N-1: no annihilator, no split
check(gcd(lift(Mod(y,N)^2)-1, N) == 1,  "k=2 | N-1: gcd(y^2-1,N)=1");
check(gcd(lift(Mod(y,N)^3)-1, N) == 1,  "k=3 | N-1: gcd(y^3-1,N)=1");
check(gcd(lift(Mod(y,N)^6)-1, N) == 1,  "k=6 | N-1: gcd(y^6-1,N)=1");
check(gcd(lift(Mod(y,N)^31)-1, N) == 1, "k=31 | N-1: gcd(y^31-1,N)=1");
check(gcd(lift(Mod(y,N)^62)-1, N) == 1, "k=62 | N-1: gcd(y^62-1,N)=1");
check(gcd(lift(Mod(y,N)^93)-1, N) == 1, "k=93 | N-1: gcd(y^93-1,N)=1");
check(lift(Mod(y,N)^186) == 157,        "y^{N-1} ≡ 157 not 1");
check(gcd(157-1, N) == 1,               "k=186: gcd(y^{N-1}-1,N)=1");

\\ Leftover x also does not leak through N-1
check(gcd(lift(Mod(x,N)^186)-1, N) == 1,"leftover x^{N-1}-1 does not split");
check(lift(Mod(x,N)^186) != 1,          "leftover x^{N-1} ≢ 1: N-1 does not certify x in <y>");

\\ N+1 divisors
check(gcd(lift(Mod(y,N)^4)-1, N) == 1,  "k=4 | N+1: gcd(y^4-1,N)=1");
check(gcd(lift(Mod(y,N)^47)-1, N) == 1, "k=47 | N+1: gcd(y^47-1,N)=1");
check(gcd(lift(Mod(y,N)^94)-1, N) == 1, "k=94 | N+1: gcd(y^94-1,N)=1");
check(lift(Mod(y,N)^188) == 16,         "y^{N+1} ≡ 16 not 1");
check(gcd(16-1, N) == 1,                "k=188: gcd(y^{N+1}-1,N)=1");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
