\\ Method 2 scale/shape supplement.  The identity is a theorem at every
\\ size; this file pins it at cryptographic bit lengths, tests public
\\ bases that are functions of N (missing from cas/43), and contrasts
\\ imbalanced primes.  A statistical leak whose bias shrinks with N
\\ is *easier* to see at 16-bit than at 2048-bit.  A structural leak
\\ that needs N-derived bases or imbalance would have been invisible
\\ to cas/43.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

setrand(44);

nbit_prime(n) = nextprime(2^(n-1) + random(2^(n-1)));

same_size_pair(n) = {
  p = nbit_prime(n); q = nbit_prime(n);
  while(p==q, q = nbit_prime(n));
  if(p<q, t=p; p=q; q=t);
  [p,q]
};

unbal_pair(np, nq) = {
  p = nbit_prime(np); q = nbit_prime(nq);
  [p,q]
};

id_at(np, nq, as, tag) = {
  pq = if(np==nq, same_size_pair(np), unbal_pair(np, nq));
  p = pq[1]; q = pq[2]; N = p*q; s = p+q;
  bad = 0;
  for(i = 1, #as, \
    a = as[i]; \
    if(type(a)=="t_VEC", a = a[1]); \
    if(lift(Mod(a,N)^(N+1)) != lift(Mod(a,N)^s), bad++); \
    if(s>=2 && lift(Mod(a,N)^(N-1)) != lift(Mod(a,N)^(s-2)), bad++) \
  );
  printf("  [id %s] Nbit=%d pbit=%d qbit=%d bad=%d\n", tag, #N, #p, #q, bad);
  bad
};

\\ ---------- 1. Identity at cryptographic size ----------
id_sized(n, tag) = {
  pq = same_size_pair(n); p = pq[1]; q = pq[2]; N = p*q; s = p+q;
  as = [0,1,-1,2,3,65537, N-1, N+1, N\2, sqrtint(N), 2*sqrtint(N), p, q];
  bad = 0;
  for(i = 1, #as, \
    a = as[i]; \
    if(lift(Mod(a,N)^(N+1)) != lift(Mod(a,N)^s), bad++) \
  );
  printf("  [id %s] #N=%d #p=%d #q=%d |p-q|bits=%d bad=%d\n", \
    tag, #N, #p, #q, #abs(p-q), bad);
  bad
};

check(id_sized(128, "128+128")==0,  "identity 128-bit primes, N-derived bases");
check(id_sized(256, "256+256")==0,  "identity 256-bit primes, N-derived bases");
check(id_sized(512, "512+512")==0,  "identity 512-bit primes, N-derived bases");
check(id_sized(1024,"1024+1024")==0, "identity 1024-bit primes, N-derived bases");
check(id_sized(2048,"2048+2048")==0, "identity 2048-bit primes, N-derived bases");

\\ One 4096-bit prime pair, a=2 and a=2√N only (each exp is heavy).
id_sparse(n, tag) = {
  pq = same_size_pair(n); p = pq[1]; q = pq[2]; N = p*q; s = p+q;
  as = [2, 2*sqrtint(N), N-1];
  bad = 0;
  for(i = 1, #as, \
    a = as[i]; \
    if(lift(Mod(a,N)^(N+1)) != lift(Mod(a,N)^s), bad++) \
  );
  printf("  [id %s] #N=%d #p=%d bad=%d\n", tag, #N, #p, bad);
  bad
};
check(id_sparse(4096, "4096+4096")==0, "identity 4096-bit primes, a=2, 2√N, N-1");

\\ 8192-bit: single base a=2.  Confirms the theorem at the size asked.
id_one(n, tag) = {
  pq = same_size_pair(n); p = pq[1]; q = pq[2]; N = p*q; s = p+q;
  bad = (lift(Mod(2,N)^(N+1)) != lift(Mod(2,N)^s));
  printf("  [id %s] #N=%d #p=%d bad=%d\n", tag, #N, #p, bad);
  bad
};
check(id_one(8192, "8192+8192")==0, "identity 8192-bit primes, a=2");

\\ ---------- 2. Imbalanced identity ----------
id_unbal(np, nq, tag) = {
  p = nbit_prime(np); q = nbit_prime(nq); N = p*q; s = p+q;
  as = [0,1,-1,2,65537, N-1, sqrtint(N), 2*sqrtint(N), p, q];
  bad = 0;
  for(i = 1, #as, \
    a = as[i]; \
    if(lift(Mod(a,N)^(N+1)) != lift(Mod(a,N)^s), bad++) \
  );
  printf("  [id %s] #p=%d #q=%d #N=%d s-2sqrtN bits=%d bad=%d\n", \
    tag, #p, #q, #N, #abs(s-2*sqrtint(N)), bad);
  bad
};
check(id_unbal(32, 96, "32+96")==0,     "identity 32-bit vs 96-bit (imbalanced)");
check(id_unbal(64, 192,"64+192")==0,    "identity 64-bit vs 192-bit");
check(id_unbal(256,1792,"256+1792")==0, "identity 256-bit vs 1792-bit (2048-bit N)");
check(id_unbal(16, 2048,"16+2048")==0,  "identity tiny p vs 2048-bit q (extreme unbalance)");

\\ N-1 ≡ -1 and N+1 ≡ 1 (mod N): g is the constant 1 (s even).
\\ That is the torsion reading already closed in cas/43, not a new bit.
const_fail = 0;
for(t = 1, 20, \
  pq = same_size_pair(32); p = pq[1]; q = pq[2]; N = p*q; \
  if(lift(Mod(N-1,N)^(N+1)) != 1, const_fail++); \
  if(lift(Mod(N+1,N)^(N+1)) != 1, const_fail++) \
);
check(const_fail == 0, "g(N-1)=g(N+1)=1 — torsion, restates s even");

\\ Real N-derived bases: not 0, ±1 mod N.
\\ cas/43 used fixed small a.  A leak that needs a = 2√N or N\2
\\ would have been invisible.  80 samples, 32-bit primes, 8 bits.
nsamp = 80; nbits = 8;
nderiv = 4;
match = matrix(nderiv, nbits);
for(t = 1, nsamp, \
  pq = same_size_pair(32); p = pq[1]; q = pq[2]; N = p*q; s = p+q; \
  as = [2*sqrtint(N), sqrtint(N), N\2, nextprime(sqrtint(N))]; \
  for(bi = 1, nderiv, \
    g = lift(Mod(as[bi], N)^(N+1)); \
    for(bg = 0, nbits-1, \
      if(bittest(g,bg)==bittest(s,bg), match[bi,bg+1] = match[bi,bg+1]+1) \
    ) \
  ) \
);
maxdev = 0; worst = "none";
for(bi = 1, nderiv, \
  for(bg = 1, nbits, \
    r = match[bi,bg]/nsamp; d = abs(r-0.5); \
    if(d > maxdev, maxdev = d; worst = Strprintf("base#%d bit %d rate=%.3f", bi, bg-1, r)) \
  ) \
);
printf("  [N-bases 32-bit] samples=%d max |rate-1/2|=%.3f at %s\n", nsamp, maxdev, worst);
check(maxdev < 0.22, "N-derived bases do not leak bits of s at 32-bit (80 samples, thresh 0.22)");

\\ 64-bit, fewer samples, three N-derived bases
ns2 = 40; match2 = matrix(3, 8);
for(t = 1, ns2, \
  pq = same_size_pair(64); p = pq[1]; q = pq[2]; N = p*q; s = p+q; \
  as = [2*sqrtint(N), N\2, sqrtint(N)]; \
  for(bi = 1, 3, \
    g = lift(Mod(as[bi], N)^(N+1)); \
    for(bg = 0, 7, \
      if(bittest(g,bg)==bittest(s,bg), match2[bi,bg+1] = match2[bi,bg+1]+1) \
    ) \
  ) \
);
maxdev2 = 0;
for(bi = 1, 3, for(bg = 1, 8, \
  r = match2[bi,bg]/ns2; d = abs(r-0.5); if(d > maxdev2, maxdev2 = d) \
));
printf("  [N-bases 64-bit] samples=%d max |rate-1/2|=%.3f\n", ns2, maxdev2);
check(maxdev2 < 0.28, "N-derived bases do not leak bits of s at 64-bit (40 samples)");

\\ ---------- 4. Imbalanced bit correlation (32 vs 96) ----------
\\ Unbalanced ⇒ s far from 2√N (AM-GM).  Fermat-in-exponent should
\\ fail *harder*, not succeed.  Confirm no new bit leak either.
ns3 = 60; match3 = matrix(4, 8);
for(t = 1, ns3, \
  p = nbit_prime(32); q = nbit_prime(96); N = p*q; s = p+q; \
  as = [2, 65537, 2*sqrtint(N), N\2]; \
  for(bi = 1, 4, \
    g = lift(Mod(as[bi], N)^(N+1)); \
    for(bg = 0, 7, \
      if(bittest(g,bg)==bittest(s,bg), match3[bi,bg+1] = match3[bi,bg+1]+1) \
    ) \
  ) \
);
maxdev3 = 0;
for(bi = 1, 4, for(bg = 1, 8, \
  r = match3[bi,bg]/ns3; d = abs(r-0.5); if(d > maxdev3, maxdev3 = d) \
));
printf("  [unbal 32+96] samples=%d max |rate-1/2|=%.3f\n", ns3, maxdev3);
check(maxdev3 < 0.24, "imbalanced 32+96: no bit of g(a) matches a bit of s");

\\ Fermat-in-exponent on imbalanced should fail (s-2√N is huge).
unbal_fermat = 0; uf_n = 8;
for(t = 1, uf_n, \
  p = nbit_prime(24); q = nbit_prime(48); N = p*q; \
  s0 = 2*sqrtint(N); if(s0%2, s0++); \
  g = lift(Mod(2,N)^(N+1)); found = 0; \
  for(k = -2^10, 2^10, \
    if(s0+k < 0, next); \
    if(lift(Mod(2,N)^(s0+k)) == g, found=1) \
  ); \
  if(found, unbal_fermat++) \
);
printf("  [unbal fermat-exp] 24+48 recovered k in ±2^10: %d/%d\n", unbal_fermat, uf_n);
check(unbal_fermat == 0, "Fermat-in-exponent fails on imbalanced (s farther from 2√N)");

\\ ---------- 5. 2048-bit identity already pinned.  Spot-check one
\\ residue is not a trivial factor.
pq = same_size_pair(256); p = pq[1]; q = pq[2]; N = p*q;
g2 = lift(Mod(2,N)^(N+1));
check(gcd(g2-1, N)==1, "gcd(2^{N+1}-1, N)=1 on a 256-bit pair");
check(g2 != 0 && g2 != 1 && g2 != N-1, "g(2) is not a trivial residue at 256-bit");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
