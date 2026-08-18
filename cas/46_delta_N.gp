\\ Method 3 — cheap Cl(Δ(N)) invariants.  No qfbclassno / h(Δ).
\\ (N,0,1) of disc −4N is SL2-equivalent to the principal form
\\ (SixthType.form_N01_equiv_principal).  Reducing it cannot split
\\ a far N.  N²−4=(N−2)(N+2) is a public factorization; gcd(N−2,N)
\\ is 1 for odd N.  Genus characters of Δ(N) are Kronecker symbols
\\ (Method 7 overlap): they do not isolate (·/p).

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

setrand(46);
nbit_prime(n) = nextprime(2^(n-1) + random(2^(n-1)));
far_pair(n, gap) = {
  for(tries = 1, 4000, \
    p = nbit_prime(n); q = nbit_prime(n); \
    if(p==q, next); \
    if(p<q, t=p; p=q; q=t); \
    if(p<=2*q && abs(p-q)>=2^gap, return([p,q])) \
  );
  error("far_pair: none")
};

\\ ---------- (N,0,1) ~ (1,0,N) ----------
red_prin = 0; split_red = 0; ns = 40;
for(t = 1, ns, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  f = Qfb(N, 0, 1); \
  r = qfbred(f); \
  id = qfbred(Qfb(1, 0, N)); \
  if(r == id, red_prin++); \
  a = component(r, 1); \
  if(a>1 && a<N && N%a==0, split_red++) \
);
\\ qfbred(Qfb(N,0,1)) is the principal reduced form.  It must not
\\ introduce a proper divisor of N on far pairs.
printf("  [red (N,0,1)] principal=%d/%d  split N=%d/%d\n", red_prin, ns, split_red, ns);
check(split_red == 0, "reducing (N,0,1) does not split far N");

\\ Close pairs: N near a square — reduction is Fermat/SQUFOF (Type A).
close_split = 0; cn = 20;
for(t = 1, cn, \
  p = nbit_prime(16); q = nextprime(p+1); N = p*q; \
  r = qfbred(Qfb(N, 0, 1)); \
  a = component(r, 1); \
  if(a>1 && a<N && N%a==0, close_split++) \
);
printf("  [red close] split N=%d/%d (principal still; Type A is CF of √N not this swap)\n", close_split, cn);
check(1, "close reduction recorded");

\\ ---------- Δ = N²−4 = (N−2)(N+2) ----------
fac_ok = 0; gcd_ok = 0;
for(t = 1, 40, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  if(N^2-4 == (N-2)*(N+2), fac_ok++); \
  if(gcd(N-2, N)==1 && gcd(N+2, N)==1, gcd_ok++) \
);
check(fac_ok==40, "N²−4 = (N−2)(N+2)");
check(gcd_ok==40, "gcd(N±2, N)=1 for odd N — genus of Δ=N²−4 does not see p");

\\ Factors of N±2 vs secrets: a secret dividing N-2 identically?
always = 1; some = 0;
for(t = 1, 40, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  hit = 0; secs = [p-1,p+1,q-1,q+1,p+q,abs(p-q)]; \
  for(si = 1, #secs, if(secs[si] && (N-2)%secs[si]==0, hit=1)); \
  if(hit, some=1, always=0) \
);
printf("  [N-2 | secret] always=%d sometimes=%d\n", always && some, some);
check(!(always && some), "N−2 is not identically a multiple of a secret");

\\ ---------- Other Δ(N): Kronecker vs bits of s (cheap genus char) ----------
deltas(N) = [-4*N, 1-4*N, 4*N-1, N^2-4, 5-4*N, -N];
maxdev = 0;
ns2 = 80;
match = matrix(6, 3); defc = matrix(6, 3);
for(t = 1, ns2, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; s = p+q; \
  ds = deltas(N); \
  for(di = 1, 6, \
    k = kronecker(ds[di], 5); \
    if(k==0, next); \
    for(bg = 1, 3, \
      defc[di,bg] = defc[di,bg]+1; \
      if((k==1) == bittest(s, bg), match[di,bg] = match[di,bg]+1) \
    ) \
  ) \
);
for(di = 1, 6, for(bg = 1, 3, \
  if(defc[di,bg]<20, next); \
  r = match[di,bg]/defc[di,bg]; d = abs(r-0.5); if(d>maxdev, maxdev=d) \
));
printf("  [kronecker Δ(N)/5 vs s bits 1–3] max |rate-1/2|=%.3f\n", maxdev);
check(maxdev < 0.22, "genus characters of Δ(N) do not pin bits of p+q");

\\ 2-rank is not computable from N without ω(Δ), which for −4N
\\ needs the factors of N.  Computing it is factoring.  Recorded.

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
