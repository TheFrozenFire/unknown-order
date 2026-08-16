\\ CAS witnesses — a non-trivial square root of 1 splits N.
\\ Mirrors nontrivial_sqrt1_splits / duality_unique_order_2_on_prime.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

N = 187;
\\ 67² ≡ 1 (mod 187), 67 ≢ ±1
check(lift(Mod(67,N)^2) == 1,           "67² ≡ 1 (mod 187)");
check(67 % N != 1 && 67 % N != N-1,     "67 ≢ ±1");
check(gcd(67-1, N) == 11,               "gcd(66,187)=11");
check(gcd(67+1, N) == 17,               "gcd(68,187)=17  (the other factor)");

\\ on a prime, the only square roots of 1 are ±1
p = 17; extra = 0;
for(x = 0, p-1, \
  if(lift(Mod(x,p)^2)==1 && x!=1 && x!=p-1, extra++) \
);
check(extra == 0,                       "unique order-2 element on the prime 17");

\\ count square roots of 1 on N=pq: there are four (±1 and the two mixed ones)
nroots = 0;
for(x = 0, N-1, if(lift(Mod(x,N)^2)==1, nroots++));
check(nroots == 4,                      "four square roots of 1 in (Z/187Z)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
