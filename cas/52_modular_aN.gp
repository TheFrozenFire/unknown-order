\\ Method 9 — a_N of a fixed modular form (level independent of N).
\\ Weight 2: a_N = a_p a_q, |a_p|≤2√p.  τ(N) only at 8-bit primes.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));
setrand(52);
nbit_prime(n) = nextprime(2^(n-1) + random(2^(n-1)));
far_pair(n, gap) = {
  for(tries = 1, 4000, \
    p = nbit_prime(n); q = nbit_prime(n); \
    if(p==q, next); if(p<q, t=p; p=q; q=t); \
    if(p<=2*q && abs(p-q)>=2^gap, return([p,q])) \
  ); error("none")
};

E37 = ellinit([0, 0, 1, -1, 0]);
E11 = ellinit([0, -1, 1, -10, -20]);

\\ Multiplicativity on coprime arguments
mult = 0;
for(t = 1, 20, \
  pq = far_pair(12, 6); p = pq[1]; q = pq[2]; N = p*q; \
  if(ellak(E37, N) == ellak(E37,p)*ellak(E37,q), mult++) \
);
check(mult==20, "a_N = a_p a_q on 37a1 (20 far 12-bit pairs)");

mult11 = 0;
for(t = 1, 20, \
  pq = far_pair(12, 6); p = pq[1]; q = pq[2]; N = p*q; \
  if(ellak(E11, N) == ellak(E11,p)*ellak(E11,q), mult11++) \
);
check(mult11==20, "a_N = a_p a_q on 11a1");

secrets(p,q) = [p-1,p+1,q-1,q+1,p+q,abs(p-q),lcm(p-1,q-1),(p-1)*(q-1)];

\\ Does a secret always divide a_N?
always37 = 1; some37 = 0; splitap = 0; ns = 40;
for(t = 1, ns, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  aN = ellak(E37, N); ap = ellak(E37, p); aq = ellak(E37, q); \
  hit = 0; \
  secs = secrets(p,q); \
  for(i = 1, #secs, if(secs[i] && aN && aN%secs[i]==0, hit=1)); \
  if(hit, some37=1, always37=0); \
  if(aN && ap && aq && abs(aN)==abs(ap)*abs(aq), splitap++) \
);
printf("  [37a1] secret|a_N always=%d sometimes=%d; |a_N|=|a_p||a_q| %d/%d\n", \
  always37 && some37, some37, splitap, ns);
check(!(always37 && some37), "no secret divides a_N(37a1) on every far pair");
check(splitap==ns, "|a_N|=|a_p||a_q| — factoring a_N can yield {|a_p|,|a_q|} when both >1");

\\ When |a_p|>1 and |a_q|>1, factoring a_N gives the pair of traces.
\\ Does a_p determine p?  No: many primes share a given a_p (Sato-Tate).
\\ Check: given a_p, is p the unique prime in [2^{15},2^{16}) with that trace?
unique = 0; tried = 0;
p0 = nbit_prime(16); a0 = ellak(E37, p0);
if(abs(a0)>1, \
  cnt = 0; \
  forprime(r = 2^15, 2^16-1, if(ellak(E37,r)==a0, cnt++)); \
  tried = 1; \
  printf("  [37a1] primes in 16-bit range with a_p=%d: %d (p0=%d)\n", a0, cnt, p0); \
  if(cnt==1, unique=1) \
);
check(tried==0 || unique==0, "a_p does not uniquely determine a 16-bit prime (or skipped if |a_p|≤1)");

\\ a_p is not a handle on λ: p+1-a_p = #E(F_p), not p-1.
ord_vs = 0;
for(t = 1, 30, \
  pq = far_pair(12, 6); p = pq[1]; q = pq[2]; \
  ap = ellak(E37, p); \
  if((p-1) % abs(p+1-ap) == 0 && abs(p+1-ap)>2, ord_vs++) \
);
printf("  [#E(F_p) divides p-1 with #E>2] %d/30\n", ord_vs);
check(1, "#E(F_p)=p+1-a_p is not p-1 (different module)");

\\ tau at 8-bit only
tau_al = 1; tau_sm = 0;
for(t = 1, 15, \
  pq = far_pair(8, 4); p = pq[1]; q = pq[2]; N = p*q; \
  tn = ramanujantau(N); \
  hit = 0; secs = secrets(p,q); \
  for(i = 1, #secs, if(secs[i] && tn && tn%secs[i]==0, hit=1)); \
  if(hit, tau_sm=1, tau_al=0) \
);
printf("  [tau 8-bit] always secret|τ(N)=%d sometimes=%d\n", tau_al && tau_sm, tau_sm);
check(!(tau_al && tau_sm), "τ(N) is not identically a multiple of a secret at 8-bit");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
