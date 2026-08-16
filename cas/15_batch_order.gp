\\ CAS witnesses — Type D without a shared prime.
\\ Mirrors BatchOrder.v: one public M splits two coprime moduli
\\ whose p-1 and p'-1 are both B-smooth.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

lcm_upto(B) = { m = 1; for(i = 2, B, m = lcm(m, i)); m };

is_smooth(n, B) = {
  if(n <= 1, return(0));
  f = factor(n);
  for(i = 1, matsize(f)[1], if(f[i,1] > B, return(0)));
  1
};

\\ primes with p-1 | M: then the public M annihilates the p-side
primes_dividing_M(B) = {
  M = lcm_upto(B);
  ds = divisors(M);
  v = [];
  for(i = 1, #ds, \
    cand = ds[i] + 1; \
    if(isprime(cand) && cand > 3, v = concat(v, [cand])) \
  );
  v
};

B = 8; M = lcm_upto(B);
ps = primes_dividing_M(B);
check(#ps >= 2,                         "at least two primes with p-1 | lcm(1..8)");
p = ps[1]; pp = ps[#ps];
if(p == pp && #ps > 1, pp = ps[2]);
q  = 23; qq = 47;
if(q==p || q==pp, q = 59);
if(qq==p || qq==pp || qq==q, qq = 61);
check(p > 1 && pp > 1 && p != pp,       "two distinct B-smooth-p-1 primes");
check(is_smooth(p-1, B) && is_smooth(pp-1, B), "both p-1 and p'-1 are 8-smooth");
check(isprime(q) && isprime(qq),        "q, q' prime");
check(p!=q && p!=qq && pp!=q && pp!=qq && q!=qq && p!=pp, "four distinct primes");

N1 = p*q; N2 = pp*qq;
check(gcd(N1, N2) == 1,                 "moduli are coprime (batch GCD sees nothing)");
check((p-1) % 1 == 0 && M % (p-1) == 0 && M % (pp-1) == 0, \
                                        "same public M annihilates both p-sides");

splitN(N, M) = {
  for(a = 2, 20, \
    if(gcd(a, N) == 1, \
      g = gcd(lift(Mod(a, N)^M) - 1, N); \
      if(g > 1 && g < N, return(g)) \
    ) \
  );
  0
};
g1 = splitN(N1, M);
g2 = splitN(N2, M);
check(g1 == p || g1 == q,               "M splits N1");
check(g2 == pp || g2 == qq,             "M splits N2");
check(g1 != 1 && g2 != 1 && g1 != 0 && g2 != 0, "neither gcd is 1");

\\ shared large r | gcd(p-1, p'-1), r not B-smooth
r = 101;
check(isprime(r),                       "r = 101 prime");
p3 = 0; p4 = 0;
for(k = 2, 400, \
  cand = 2*r*k + 1; \
  if(isprime(cand), if(!p3, p3 = cand, if(cand != p3, p4 = cand; break))) \
);
check(p3 && p4,                         "two primes ≡ 1 (mod 101)");
check((p3-1) % r == 0 && (p4-1) % r == 0, "r | p-1 and r | p'-1");
check(gcd(p3-1, p4-1) % r == 0,         "r | gcd(p-1, p'-1)");
N3 = p3*q; N4 = p4*qq;
check(gcd(N3, N4) == 1,                 "still no shared N-factor");
check(p3 % r == 1 && p4 % r == 1,       "both primes sit on the AP X ≡ 1 (mod r)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
