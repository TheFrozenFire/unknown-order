\\ Public tests of e vs residual tests (which mention λ), and E(N,y)
\\ algorithm classes beyond constant e and e=X.
\\ Mirrors FilterShape.v (public tests) and SolverRestrict.v (E classes).
\\ Residual leaf named, not solved.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p=11; q=17; N=p*q; lam=80; y=36; x=42; ee=3;

\\ --- residual tests mention λ ---
check(ee % 2 == 1,                      "residual: e=3 is odd");
check(gcd(ee, lam) == 1,                "residual: gcd(3,λ)=1");
check((ee-1) % lam != 0,                "residual: λ does not divide e-1");
check(gcd(5, lam) == 5,                 "e=5 shares λ: not residual");
check(gcd(15, lam) == 5,                "e=15 odd but shares λ");
check(gcd(7, lam) == 1 && 7%2==1 && (7-1)%lam != 0, "e=7 is residual-shaped");

\\ --- public test already named: gcd(e, N-1)=1 rejects the cube ---
check(gcd(3, N-1) == 3,                 "gcd(e,N-1)=1 rejects the cube");
check(gcd(5, N-1) == 1,                 "gcd(5,N-1)=1: public filter accepts a non-residual e");
check(gcd(7, N-1) == 1,                 "gcd(7,N-1)=1: public filter also accepts residual e=7");
check(gcd(3, N-1) != 1,                 "public N-1 filter does not certify residual");

\\ --- invertibility modulo a public integer other than λ: gcd(e,N)=1 ---
check(gcd(3, N) == 1,                   "gcd(e,N)=1: cube passes");
check(gcd(5, N) == 1,                   "gcd(5,N)=1: non-residual e=5 also passes");
check(gcd(15, N) == 1,                  "gcd(15,N)=1: odd λ-sharing e also passes");
check(gcd(5, lam) != 1,                 "gcd(e,N)=1 does not certify residual");

\\ --- other (N,y)-only predicate: gcd(e, φ(y))=1 ---
phi_y = eulerphi(y);
check(phi_y == 12,                      "φ(y)=12 is a function of y alone");
check(gcd(3, phi_y) == 3,               "gcd(e,φ(y))=1 rejects the cube");
check(gcd(3, phi_y) != 1,               "φ(y)-filter is (N,y)-only and rejects e=3");

\\ --- quadratic E(N,y): e = y^2+1, degree 2 ---
e_quad = y^2 + 1;
check(e_quad == 1297,                   "P=1+Y^2: P(36)=1297");
check(e_quad % 2 == 1,                  "quadratic e is odd");
check(gcd(e_quad, lam) == 1,            "gcd(1297,λ)=1 residual-shaped");
check((e_quad-1) % lam != 0,            "λ does not divide 1296");
x_quad = lift(Mod(y,N)^33);
check(x_quad == 104,                    "period inverse: y^{33} ≡ 104");
check(lift(Mod(x_quad,N)^e_quad) == y,  "104^{1297} ≡ 36 leftover if you have ord");
check(lift(Mod(y,N)^e_quad) == 53,      "write-e-then-x: y^e ≡ 53 encrypt, not invert");
check(53 != 104,                        "encrypt-as-decrypt is not leftover x");
check(lift(Mod(y,N)^N) == 42,           "named accident y^N ≡ 42 is the e=3 root, not 104");
check(42 != 104,                        "y^N accident does not hit this leftover x");

\\ --- degree-2 that peels: e = y^2 even ---
check((y^2) % 2 == 0,                   "e=y^2 is even: peels");

\\ --- constant e is RSA at that e, not a Strong-RSA class ---
check(lift(Mod(x,N)^3) == y,            "constant e=3 cube root is RSA at e=3");
check(3 == 3,                           "constant P=[3] is fixed e");

\\ --- rejection-sample odd primes against gcd(e,N-1)=1 ---
check(gcd(3, N-1) != 1,                 "sample: e=3 rejected by public filter");
check(gcd(5, N-1) == 1,                 "sample: first accepted odd prime is 5");
check(gcd(5, lam) == 5,                 "rejection sample emits non-residual e=5");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
