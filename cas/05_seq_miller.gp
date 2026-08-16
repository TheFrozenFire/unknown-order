\\ CAS witnesses — sequential-base Miller (primes 2,3,5,...).
\\ Deterministic; we do not claim the ERH polynomial bound.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

oddpart(n) = { while(n%2==0, n = n/2); n };
val2(n) = valuation(n, 2);
miller_factor(N, M, a) = {
  t = oddpart(M); s = val2(M);
  g = lift(Mod(a,N)^t);
  if(g==1, return(0));
  for(i = 1, s, \
    ng = lift(Mod(g,N)^2); \
    if(ng==1, \
      if(g!=1 && g!=N-1, return(gcd(g-1, N)), return(0)) \
    ); \
    g = ng \
  );
  0
};

seq_miller(N, M, nprimes) = {
  P = primes(nprimes);
  for(i = 1, #P, \
    if(gcd(P[i],N)==1, \
      f = miller_factor(N, M, P[i]); \
      if(f>1 && f<N, return([P[i], f])) \
    ) \
  );
  [0,0]
};

N = 187; M = 80;
res = seq_miller(N, M, 10);
check(res[1] == 2,                      "first successful prime base is 2");
check(res[2]==11 || res[2]==17,         "it returns a prime factor of 187");

\\ random instances: the first few primes almost always suffice
setrand(3);
late = 0; miss = 0;
for(t = 1, 30, \
  p = nextprime(80 + random(120)); q = nextprime(80 + random(120)); \
  if(p==q, next); \
  NN = p*q; ee = 3; \
  if(gcd(ee, lcm(p-1,q-1))!=1, next); \
  dd = lift(1/Mod(ee, lcm(p-1,q-1))); \
  MM = ee*dd - 1; \
  r = seq_miller(NN, MM, 20); \
  if(r[2]==0, miss++, if(r[1] > 5, late++)) \
);
check(miss == 0,                        "first 20 primes always split 30 random instances");
printf("  [index] bases > 5 needed on %d instances (informational)\n", late);

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
