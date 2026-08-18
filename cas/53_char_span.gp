\\ Method 10 — K public characters as an F_2-vector.
\\ +1↦0, −1↦1.  Every F_2-linear form is a subset XOR = subset product.
\\ A hit is a form that equals (5/p) on every far pair.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));
setrand(53);
nbit_prime(n) = nextprime(2^(n-1) + random(2^(n-1)));
far_pair(n, gap) = {
  for(tries = 1, 4000, \
    p = nbit_prime(n); q = nbit_prime(n); \
    if(p==q, next); if(p<q, t=p; p=q; q=t); \
    if(p<=2*q && abs(p-q)>=2^gap, return([p,q])) \
  ); error("none")
};

oddprimes(K) = {
  v = []; x = 3;
  while(#v < K, if(isprime(x), v = concat(v,[x])); x += 2);
  v
};

bitof(k) = if(k==1, 0, if(k==-1, 1, -1));

K = 16; ells = oddprimes(K);
ns = 40;
\\ pub[t, i] = (ells[i]/N_t) as 0/1; skip samples with a 0 Kronecker
\\ Accumulate, for each mask, how many samples match (5/p)
match = vector(2^K);
okn = 0;
for(t = 1, ns, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  good = 1; bits = vector(K); \
  for(i = 1, K, \
    kr = kronecker(ells[i], N); \
    b = bitof(kr); \
    if(b<0, good=0); \
    bits[i] = b \
  ); \
  tgt = bitof(kronecker(5, p)); \
  if(tgt<0 || !good, next); \
  okn++; \
  for(mask = 0, 2^K-1, \
    v = 0; \
    for(i = 1, K, if(bittest(mask, i-1), v = bitxor(v, bits[i]))); \
    if(v==tgt, match[mask+1] = match[mask+1]+1) \
  ) \
);
printf("  [span] usable samples=%d  K=%d forms=%d\n", okn, K, 2^K);
full = 0; best = 0; bestm = 0;
for(mask = 0, 2^K-1, \
  if(match[mask+1] > best, best = match[mask+1]; bestm = mask); \
  if(okn && match[mask+1]==okn, full++) \
);
printf("  [span] forms identical to (5/p) on all samples: %d; best %d/%d (mask=%d)\n", \
  full, best, okn, bestm);
check(okn >= 20, "enough samples with no zero Kronecker");
check(full==0, "no F_2-linear form of K=16 public (ℓ/N) is identically (5/p)");

\\ Also vs (13/p) so it is not 5-specific
match2 = vector(2^K); okn2 = 0;
for(t = 1, ns, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  good = 1; bits = vector(K); \
  for(i = 1, K, \
    b = bitof(kronecker(ells[i], N)); \
    if(b<0, good=0); bits[i] = b \
  ); \
  tgt = bitof(kronecker(13, p)); \
  if(tgt<0 || !good, next); \
  okn2++; \
  for(mask = 0, 2^K-1, \
    v = 0; \
    for(i = 1, K, if(bittest(mask, i-1), v = bitxor(v, bits[i]))); \
    if(v==tgt, match2[mask+1] = match2[mask+1]+1) \
  ) \
);
full2 = 0;
for(mask = 0, 2^K-1, if(okn2 && match2[mask+1]==okn2, full2++));
printf("  [span vs (13/p)] identical forms=%d on %d samples\n", full2, okn2);
check(full2==0, "no F_2-linear form is identically (13/p) either");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
