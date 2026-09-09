\\ Pratt verifier given a factorization of p-1.  p=31, g=3,
\\ qs=[2;3;5], 30=2*3*5.  Completeness for every prime (exists
\\ factorization) is pratt_complete_open_named.  Mirrors
\\ pratt_generator_ok_31 / pratt_factors_ok_31 /
\\ pratt_verified_implies_prime.  gcd form is the soundness
\\ check; Fermat-alone is not (Carmichael 561).
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

check(lift(Mod(3,31)^30)==1,            "3^30 cong 1 mod 31");
check(lift(Mod(3,31)^15)!=1,            "3^{30/2} is not 1");
check(lift(Mod(3,31)^10)!=1,            "3^{30/3} is not 1");
check(lift(Mod(3,31)^6)!=1,             "3^{30/5} is not 1");
check(gcd(lift(Mod(3,31)^15)-1, 31)==1, "gcd(3^{15}-1, 31)=1");
check(gcd(lift(Mod(3,31)^10)-1, 31)==1, "gcd(3^{10}-1, 31)=1");
check(gcd(lift(Mod(3,31)^6)-1, 31)==1,  "gcd(3^6-1, 31)=1");
check(isprime(2),                       "2 is prime");
check(isprime(3),                       "3 is prime");
check(isprime(5),                       "5 is prime");
check(isprime(31),                      "31 is prime");
check(2*3*5==30,                        "factors of 30 are 2, 3, 5");
check(lift(Mod(2,5)^4)==1,              "2^4 cong 1 mod 5");
check(lift(Mod(2,5)^2)!=1,              "2^{4/2} is not 1 mod 5");
check(lift(Mod(2,3)^2)==1,              "2^2 cong 1 mod 3");
check(lift(Mod(2,3)^1)!=1,              "2^{2/2} is not 1 mod 3");
check(gcd(lift(Mod(2,11)^5)-1, 11)==1,  "gcd(2^5-1, 11)=1");
check(gcd(lift(Mod(2,11)^2)-1, 11)==1,  "gcd(2^2-1, 11)=1");
check(lift(Mod(2,561)^560)==1,          "Carmichael Fermat side holds");
check(gcd(lift(Mod(2,561)^280)-1, 561)!=1, "Carmichael gcd form rejects");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
