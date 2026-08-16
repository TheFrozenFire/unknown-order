\\ CAS witnesses — shared primes: gcd(N1, N2) IS the common CRT component.
\\ Mirrors SharedPrime.v.  Unique factorization, not a search.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 11; q1 = 17; q2 = 19;
N1 = p*q1; N2 = p*q2;
check(N1 == 187 && N2 == 209,           "N1=11*17, N2=11*19");
check(gcd(N1, N2) == p,                 "gcd(187,209) = 11");
check(N1 % gcd(N1,N2) == 0,             "g | N1");
check(N2 % gcd(N1,N2) == 0,             "g | N2");
check(gcd(q1, q2) == 1,                 "other primes coprime");

\\ a second pair, larger
p3 = 7919; q3 = 7907; q4 = 7919+12; while(!isprime(q4), q4++);
N3 = p3*q3; N4 = p3*q4;
check(isprime(p3) && isprime(q3) && isprime(q4), "three distinct primes");
check(q3 != q4 && p3 != q3 && p3 != q4, "all distinct");
check(gcd(N3, N4) == p3,                "gcd of two moduli sharing 7919");

\\ independent moduli: gcd is 1
Na = 11*17; Nb = 13*19;
check(gcd(Na, Nb) == 1,                 "independent moduli are coprime");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
