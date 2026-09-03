\\ Algorithm classes for writing x: public addition chain, polynomial X,
\\ short public bases without SAGM-known exponents, gcd-free bounded
\\ multiply from y.  Mirrors SolverShape.v.  Residual leaf named, not
\\ solved.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; y=36; x=42;

\\ --- public addition chain for public e=3 (Hamming 2) ---
check(3 == 2+1,                         "public e=3 has Hamming 2");
check(lift(Mod(y,N)^2) == 174,          "chain: y^2 ≡ 174");
check(lift(Mod(y,N)^2 * Mod(y,N)) == 93,"chain: y^2 * y ≡ 93 = y^3");
check(93 != 42,                         "Hamming-2 chain is not leftover x");
check(lift(Mod(93,N)^3) != y,           "y^3 as x does not invert");

\\ trapdoor d=27 Hamming 4 does hit leftover x (period inverse)
check(27 == 16+8+2+1,                   "trapdoor d=27 has Hamming 4");
check(lift(Mod(y,N)^27) == 42,          "trapdoor chain y^{27} is leftover x");

\\ --- polynomial X of degree 2: x = 1+y^2 ---
xq = (1 + y*y) % N;
check(1 + y*y == 1297,                  "P=1+Y^2: P(36)=1297");
check(xq == 175,                        "1+y^2 ≡ 175 (mod N)");
check(lift(Mod(xq,N)^3) == 142,         "175^3 ≡ 142 not 36");
check(142 != 36,                        "quadratic X is not a cube root");
check(gcd(142-36, N) == 1,              "quadratic X does not one-sided split");

\\ --- short public bases {2,3} with public exponents, not SAGM a=d ---
check(lift(Mod(2,N)*Mod(3,N)) == 6,     "public bases: 2·3 ≡ 6");
check(lift(Mod(6,N)^3) == 29,           "6^3 ≡ 29 not 36");
check(29 != 36,                         "2^1 3^1 is not a cube root of y");
check(lift(Mod(2,N)^3) == 8,            "public e as exponent on base 2: 2^3 ≡ 8");
check(8 != 42,                          "2^e is not leftover x of y");
check(lift(Mod(2,N)^27) == 161,         "SAGM-known a=d on base 2 is 161, other instance");
check(161 != 42,                        "SAGM of 2 is not leftover of 36");

\\ --- gcd-free bounded multiply from y (no gcd with N) ---
check(y != x,                           "len 1: output y is not leftover x");
check(lift(Mod(y,N)*Mod(y,N)) == 174,   "len 2: y·y ≡ 174");
check(174 != 42,                        "len 2 does not hit leftover x");
check(lift(Mod(174,N)*Mod(y,N)) == 93,  "len 3: y^2·y ≡ 93");
check(93 != 42,                         "len 3 does not hit leftover x");

\\ --- public Euler-wrong exponent does not test x in <y> ---
check(lift(Mod(x,N)^40) == 1,           "trapdoor: leftover x^{ord(y)} ≡ 1");
check(lift(Mod(x,N)^186) == 64,         "public: leftover x^{N-1} ≡ 64 not 1");
check(64 != 1,                          "N-1 does not certify membership in <y>");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
