\\ Method 6 — cyclotomic / exponential gcd / smooth kernel of N±1.
\\ gcd(N-1, p-1)=gcd(p-1,q-1) usually 2.  Smooth factors of N±1
\\ dividing p-1 above the random model, identically, would be a hit.
\\ p-1 | q-1 is a generation condition, not a function of N.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));
setrand(49);
nbit_prime(n) = nextprime(2^(n-1) + random(2^(n-1)));
far_pair(n, gap) = {
  for(tries = 1, 4000, \
    p = nbit_prime(n); q = nbit_prime(n); \
    if(p==q, next); if(p<q, t=p; p=q; q=t); \
    if(p<=2*q && abs(p-q)>=2^gap, return([p,q])) \
  ); error("none")
};

smooth_part(n, B) = {
  s = 1; m = n;
  forprime(r = 2, B, \
    while(m%r==0, s = s*r; m = m/r) \
  );
  s
};

\\ gcd(N-1, p-1) = gcd(q, p-1) wait: N≡q (mod p-1) so
\\ gcd(N-1, p-1)=gcd(q-1, p-1).
g2 = 0; ns = 80;
for(t = 1, ns, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  if(gcd(N-1, p-1) == gcd(q-1, p-1), g2++) \
);
check(g2==ns, "gcd(N-1,p-1)=gcd(q-1,p-1)");

\\ Usual value is 2 (odd primes).
usual_small = 0;
for(t = 1, ns, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; \
  if(gcd(p-1, q-1) <= 16, usual_small++) \
);
printf("  [gcd(p-1,q-1)≤16] %d/%d\n", usual_small, ns);
check(usual_small > ns*3\4, "gcd(p-1,q-1) is small (≤16) on most far pairs");

\\ Smooth kernel of N-1: after peeling B-smooth, does the smooth
\\ part identically share a large factor with p-1?
B = 100; always = 1; some = 0;
for(t = 1, 50, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  sm = smooth_part(N-1, B); \
  g = gcd(sm, p-1); \
  if(g>2, some=1, always=0) \
);
printf("  [smooth_{%d}(N-1) ∩ (p-1) > 2] always=%d sometimes=%d\n", B, always && some, some);
check(!(always && some), "smooth part of N-1 is not identically a large factor of p-1");

always2 = 1; some2 = 0;
for(t = 1, 50, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  sm = smooth_part(N+1, B); \
  g = gcd(sm, p+1); \
  if(g>2, some2=1, always2=0) \
);
printf("  [smooth_{%d}(N+1) ∩ (p+1) > 2] always=%d sometimes=%d\n", B, always2 && some2, some2);
check(!(always2 && some2), "smooth part of N+1 is not identically a large factor of p+1");

\\ Φ_k(N) factors vs p-1: already Method 1 (no identity).

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
