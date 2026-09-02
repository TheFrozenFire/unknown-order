\\ Public tests of leftover x vs residual language (which mentions ord/λ).
\\ Jacobi +1 does not certify; search without e has index slack;
\\ forbidden-coset representatives do not split by gcd(x-a,N).
\\ Mirrors FilterShape.v / SrsaResidual.v.  Residual leaf named, not solved.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p=11; q=17; N=p*q; y=36; x=42;

check(kronecker(x, N) == 1,             "leftover x has Jacobi +1");
check(kronecker(y, N) == 1,             "challenge y has Jacobi +1");
check(kronecker(x, p) == 1,             "leftover x is QR mod p");
check(kronecker(x, q) == 1,             "leftover x is QR mod q");
check(kronecker(10, N) == 1,            "10 has Jacobi +1");
check(kronecker(10, p) == -1,           "10 is QNR mod p");
check(kronecker(10, q) == -1,           "10 is QNR mod q: Jacobi +1 without QR both sides");
check(lift(Mod(10,N)^3) != y,           "10 is not a cube root of y");
check(znorder(Mod(10,N)) == 16,         "10 has order 16, not a residual generator");
check(kronecker(2, N) == -1,            "2 has Jacobi -1: public filter rejects it");
check(2 != x,                           "Jacobi -1 unit is not leftover x");

check(eulerphi(N) == 160,               "160 units");
check(160 / 2 == 80,                    "Jacobi +1 is index 2: 80 candidates");
check(znorder(Mod(y,N)) == 40,          "|<y>|=40");
check(160 / 40 == 4,                    "index [units:<y>]=4");
check(eulerphi(40) == 16,               "16 generators of <y>");
check(80 / 16 == 5,                     "Jacobi +1 search slack 80/16=5 vs leftover generators");

check(gcd(x-10, N) == 1,                "gcd(x-10,N)=1: coset rep 10 does not split");
check(gcd(x-2, N) == 1,                 "gcd(x-2,N)=1: coset rep 2 does not split");
check(lift(Mod(x,N)^3) == y,            "checking x^3≡y is public at fixed e=3 (RSA uniqueness)");
check(lift(Mod(10,N)^3) != y,           "without e=3, Jacobi +1 does not pick the cube root");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
