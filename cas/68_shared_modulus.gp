\\ DKG shared modulus and biprimality via √1 count.  Mirrors SharedModulus.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p1 = 6; p2 = 5; q1 = 8; q2 = 9;
N = (p1+p2)*(q1+q2);
check(N == 11*17, "N = (p1+p2)(q1+q2) is the RSA modulus");
check(N == p1*q1 + p1*q2 + p2*q1 + p2*q2, "cross terms");

\\ publishing p+q with N factors
s = 11+17; phi = N - s + 1;
check(phi == 10*16, "N-(p+q)+1 = φ");
disc = s^2 - 4*N;
check(issquare(disc), "published (N, p+q) is a square discriminant");

\\ four √1 on biprime, eight on triprime
n2 = 0; N2 = 11*17;
for(x = 0, N2-1, if(lift(Mod(x,N2)^2)==1, n2++));
check(n2 == 4, "biprime has four √1");
n3 = 0; N3 = 11*13*17;
for(x = 0, N3-1, if(lift(Mod(x,N3)^2)==1, n3++));
check(n3 == 8, "triprime has eight √1 — not an RSA modulus");
xpm = lift(chinese([Mod(1,11), Mod(12,13), Mod(1,17)]));
check(gcd(xpm-1, N3) > 1 && gcd(xpm-1, N3) < N3, "mixed triple-root splits pqr");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
