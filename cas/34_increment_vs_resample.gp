\\ CAS — increment from kmin always hits the first prime; resample can hit later.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

a = 13099; M = 103740;
first = -1; second = -1;
for(k = 0, 40, p = a + k*M; if(isprime(p), if(first<0, first=k, if(second<0, second=k))));
check(first >= 0 && second > first,      "two primes in the walk");
check(first == 0 && second == 2,         "CAS 28: first=0 (13099), second=2 (220579)");
check(isprime(a+first*M) && isprime(a+second*M), "both prime");

\\ increment from 0 cannot return the later prime
later_is_first_from_0 = 1;
for(j = 0, second-1, if(isprime(a+j*M), later_is_first_from_0 = 0));
check(!later_is_first_from_0,            "increment from 0 hits the earlier prime first");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
