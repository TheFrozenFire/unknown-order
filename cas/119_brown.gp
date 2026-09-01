\\ Brown SLP-solver: polynomial identity vs functional-on-units.
\\ Mirrors BrownSLP.v.
\\ X^d with ed≡1 (mod λ) solves low-e RSA on units and is a short SLP.
\\ X^{81}-X is not the zero polynomial (mod 11 or over Z).
\\ Dual-number tangent is 81 y^{80}, not 1; gcd(80,187)=1 (honest: no split).
\\ Inspected object is the solver SLP, not a reduction-with-oracle (not BV).

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 11; q = 17; N = p*q; ee = 3; d = 27; lam = 80;

\\ functional: 36^{27} ≡ 42, 42^3 ≡ 36
check(lift(Mod(36,N)^d) == 42,          "X^d is a cube-root map on the test vector");
check(lift(Mod(42,N)^ee) == 36,         "roundtrip");

\\ X^{81}-X is the zero *function* on (Z/NZ)* but not the zero polynomial
check(lift(Mod(2,N)^(lam+1)) == 2,      "2^{81} ≡ 2 (mod N)  Carmichael");
check(lift(Mod(2,p)^81) == 2 % p,       "Fermat on p");
\\ polynomial X^{81}-X has leading coeff 1, linear coeff -1
check(1 % p != 0,                       "leading coeff 1 ≢ 0 (mod 11)");
check((-1) % p != 0,                    "linear coeff -1 ≢ 0 (mod 11)");

\\ dual numbers: (y+ε)^n = y^n + n y^{n-1} ε, ε^2=0
\\ F(X)=X^{27}: F(y+ε) = y^{27} + 27 y^{26} ε
\\ cube: y^{81} + 81 y^{80} ε  vs  y + ε  wants tangent 1
y = 2;
check(81 * lift(Mod(y,N)^lam) % N == 81, "tangent 81 y^{80} ≡ 81 (mod N)");
check(81 % N != 1,                      "81 ≢ 1: dual identity does not hold");
check(gcd(81-1, N) == 1,                "gcd(80,187)=1  this extension does not split");

\\ a low-degree identity would require N | -1, which it does not
check(gcd(1, N) == 1,                   "N does not divide the linear coeff -1");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
