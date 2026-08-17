\\ CAS witnesses — slot encoding.  Mirrors HashSlot.v week 1.
\\ Every seed lands on the constructor AP.  Accept is isprime.
\\ A control prime off the AP shows primality is not membership.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

r = 3; s = 5; u = 7; v = 13; w = 19;
M = 4*r*s*u*v*w;
a = 13099;
check(M == 103740 && a == 13099,         "CAS 28 slot");

in_slot(p) = p%r==1 && p%s==s-1 && p%4==3 && (p*p+p+1)%u==0 && (p*p+1)%v==0 && (p*p-p+1)%w==0;

n_prime = 0; n_comp = 0; all_in = 1; rulers_on_primes = 1; only_prime_fails = 1;
for(seed = 0, 20, p = a + seed*M; if(!in_slot(p), all_in = 0); if(isprime(p), n_prime++; if(!in_slot(p), rulers_on_primes = 0), n_comp++; if(!in_slot(p), only_prime_fails = 0)));

check(all_in,                            "seeds 0..20 all land in the slot");
check(n_prime >= 2,                      "at least two primes in 0..20");
check(rulers_on_primes,                  "every accepted (prime) output passes the rulers");
check(only_prime_fails,                  "every composite output still satisfies the rulers");

p0 = a + 0*M; p2 = a + 2*M;
check(p0 == 13099 && isprime(p0),        "seed 0 is 13099, prime");
check(p2 == 220579 && isprime(p2),       "seed 2 is 220579, prime");
check(in_slot(p0) && in_slot(p2),        "accepted outputs stay in the slot");

ctrl = 19;
check(isprime(ctrl),                     "19 is prime");
check(ctrl % M != a,                     "19 is not on the AP");
check(!in_slot(ctrl),                    "off-AP prime fails a ruler: primality is not membership");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
