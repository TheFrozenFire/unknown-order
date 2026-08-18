\\ Method 7 — character families.  (D/N)=(D/p)(D/q).  A hit is a
\\ public family {D_i(N)} whose combination equals (D/p) alone, or
\\ enough bits of p for Coppersmith.  Product-only is QR, not a factor.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));
setrand(50);
nbit_prime(n) = nextprime(2^(n-1) + random(2^(n-1)));
far_pair(n, gap) = {
  for(tries = 1, 4000, \
    p = nbit_prime(n); q = nbit_prime(n); \
    if(p==q, next); if(p<q, t=p; p=q; q=t); \
    if(p<=2*q && abs(p-q)>=2^gap, return([p,q])) \
  ); error("none")
};

\\ Product identity
prod_ok = 0; ns = 80;
for(t = 1, ns, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  D = 5; \
  if(kronecker(D,N) == kronecker(D,p)*kronecker(D,q), prod_ok++) \
);
check(prod_ok==ns, "(D/N)=(D/p)(D/q)");

\\ Can any combination of (D_i/N) for D_i in a public list recover (5/p)?
\\ Public list: small primes, and Δ(N) from Method 3.
recover = 0;
for(t = 1, ns, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  pubs = [kronecker(5,N), kronecker(13,N), kronecker(17,N), \
          kronecker(-4*N,5), kronecker(1-4*N,5), kronecker(-N,5)]; \
  target = kronecker(5,p); \
  found = 0; \
  for(mask = 1, 2^#pubs-1, \
    v = 1; \
    for(i = 1, #pubs, if(bittest(mask, i-1), v = v*pubs[i])); \
    if(v == target, found=1) \
  ); \
  if(found, recover++) \
);
printf("  [subset product of 6 public chars == (5/p)] %d/%d\n", recover, ns);
\\ Chance: 6 bits, 63 nonempty products, random ±1, P(hit) is high!
\\ ~1-(1/2)^something but products are dependent.  If recover==ns,
\\ the family *always* contains (5/p), which would be a leak.
check(recover < ns, "no fixed subset product of the public family is identically (5/p)");

\\ Correlation of each public char with (5/p)
maxdev = 0;
mc = vector(6);
for(t = 1, ns, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  pubs = [kronecker(5,N), kronecker(13,N), kronecker(17,N), \
          kronecker(-4*N,5), kronecker(1-4*N,5), kronecker(-N,5)]; \
  tgt = kronecker(5,p); \
  for(i = 1, 6, if(pubs[i]==tgt, mc[i]++)) \
);
for(i = 1, 6, \
  r = mc[i]/ns; d = abs(r-0.5); if(d>maxdev, maxdev=d); \
  printf("  [char %d vs (5/p)] rate=%.3f\n", i, r) \
);
check(maxdev < 0.22, "no single public character equals (5/p) above chance");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
