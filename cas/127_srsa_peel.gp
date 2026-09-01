\\ Strong-RSA witness peel on N=187 (and safeprime-shaped N=77).
\\ Mirrors StrongRSAPeel.v.  Residual leaf is named, not solved.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 11; q = 17; N = p*q; lam = lcm(p-1, q-1);

\\ non-unit x: 11^3 ≡ 22, gcd(11,N)=11
check(lift(Mod(11,N)^3) == 22,          "non-unit x=11, 11^3 ≡ 22");
check(gcd(11, N) == 11,                 "gcd(x,N)=11 proper factor");
check(gcd(22, N) == 11,                 "y is also non-unit");

\\ unit y forces unit x: 42^3 ≡ 36, both units
check(gcd(42,N)==1 && gcd(36,N)==1,     "cube-root witness is units");
check(lift(Mod(42,N)^3) == 36,          "Problem_StrongRSA(187,36,42,3)");

\\ Jacobi (y/N)=-1 forces odd e
check(kronecker(2,N) == -1,             "(2/187)=-1");
check(kronecker(36,N) == 1,             "(36/187)=1  (a square)");
check(lift(Mod(2,N)^81) == 2,           "λ-type: 2^{81} ≡ 2, e=81 odd");
check(81 % 2 == 1,                      "81 is odd");

\\ even e: 6^2 ≡ 36, so 36 is a square and 6 is a square root
check(lift(Mod(6,N)^2) == 36,           "even e=2: 6^2 ≡ 36");
check(lift(Mod(181,N)^2) == 36,         "associate -6=181 also squares to 36");
check(gcd(181-6, N) == N || gcd(181+6, N) == N, "associate ± does not split");
\\ mixed root of 36: 28^2 ≡ 36, gcd(28-6,N)=11
check(lift(Mod(28,N)^2) == 36,          "mixed root 28^2 ≡ 36");
check(gcd(28-6, N) == 11,               "non-associate gcd(22,187)=11");

\\ x ≡ y annihilator: y^e ≡ y ⇒ y^{e-1} ≡ 1 on units
check(lift(Mod(2,N)^81) == 2,           "x=y=2, e=81");
check(lift(Mod(2,N)^80) == 1,           "2^{80} ≡ 1");
check(lam == 80,                        "λ=80");
check(80 % 80 == 0,                     "λ | e-1");

\\ miller on M=e-1=80, base 2: 67^2 ≡ 1, gcd(66,N)=11
check(lift(Mod(67,N)^2) == 1,           "67^2 ≡ 1");
check(67 != 1 && 67 != N-1,             "67 ≢ ±1");
check(gcd(67-1, N) == 11,               "Miller split from λ-type e-1");

\\ residual leaf: (42,3) on y=36 — odd, gcd(e,λ)=1, λ ndiv e-1
check(3 % 2 == 1,                       "e=3 odd");
check(gcd(3, lam) == 1,                 "gcd(3,80)=1");
check((3-1) % lam != 0,                 "e-1=2 is not a multiple of λ");
check(lift(Mod(42,N)^3) == 36,          "genuine cube root, not λ-type");

\\ self-randomization: fixed e preserves; poly e=y does not
r = 2; ee = 3; x = 42; y = 36;
yp = lift(Mod(y,N) * Mod(r,N)^ee);
xp = lift(Mod(x,N) * Mod(r,N));
check(lift(Mod(xp,N)^ee) == yp,         "fixed-e rerand: (xr)^e ≡ y r^e");
check(y * r^ee != y,                    "poly e=X: e(y r^e) ≠ e(y) at this pin");

\\ related y and y^2: 42^{6} ≡ 36^2
check(lift(Mod(42,N)^(2*3)) == lift(Mod(36,N)^2), "x1^{2 e1} ≡ y^2");

\\ safeprime-shaped N=7*11=77, λ=lcm(6,10)=30=2*3*5
ps = 7; qs = 11; Ns = ps*qs; lams = lcm(ps-1, qs-1);
check(Ns == 77 && lams == 30,           "safeprime pin N=77, λ=30=2 p' q'");
check(isprime((ps-1)/2) && isprime((qs-1)/2), "p'=3, q'=5 prime");
check(lift(Mod(2,Ns)^(lams+1)) == 2,    "λ-type on 77: 2^{31} ≡ 2");
check(lift(Mod(2,Ns)^lams) == 1,        "2^{30} ≡ 1 (mod 77)");
\\ miller M=30=2*15, g0=2^15 mod 77
g0 = lift(Mod(2,Ns)^15);
ng = lift(Mod(g0,Ns)^2);
check(ng == 1,                          "g0^2 ≡ 1 (mod 77)");
check(g0 != 1 && g0 != Ns-1,            "g0 ≢ ±1");
check(gcd(g0-1, Ns) > 1 && gcd(g0-1, Ns) < Ns, "Miller split on safeprime λ");

\\ SAGM handle evaluates to a residue that still peels
g = 3; h = 5;
yS = lift(Mod(g,N)^2 * Mod(h,N)^1);
check(gcd(yS, N) == 1,                  "SAGM (2,1) is a unit");
check(lift(Mod(yS,N)^(lam+1)) == yS,    "λ-type peel still applies to the evaluated handle");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
