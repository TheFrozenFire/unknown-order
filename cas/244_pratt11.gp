\\ Verified Pratt check on p=11: g=2, p-1=2*5.
\\ Mirrors pratt_generator_ok_11 / pratt_factors_ok_11.
\\ Completeness for every prime is pratt_complete_open_named.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

check(lift(Mod(2,11)^10)==1,            "2^10 cong 1 mod 11");
check(lift(Mod(2,11)^5)!=1,             "2^{10/2} is not 1");
check(lift(Mod(2,11)^2)!=1,             "2^{10/5} is not 1");
check(isprime(2),                       "2 is prime");
check(isprime(5),                       "5 is prime");
check(2*5==10,                          "factors of 10 are 2 and 5");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
