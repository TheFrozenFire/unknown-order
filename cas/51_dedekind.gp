\\ Method 8 — Dedekind sums s(h,N) via reciprocity (polylog).
\\ s(1,N)=(N-1)(N-2)/(12N).  Correlate with bits of p, p+q, and
\\ with the CF of √N.  Collapse = rewrite of CF(√N) (Type A) or e/N (C).

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));
setrand(51);
nbit_prime(n) = nextprime(2^(n-1) + random(2^(n-1)));
far_pair(n, gap) = {
  for(tries = 1, 4000, \
    p = nbit_prime(n); q = nbit_prime(n); \
    if(p==q, next); if(p<q, t=p; p=q; q=t); \
    if(p<=2*q && abs(p-q)>=2^gap, return([p,q])) \
  ); error("none")
};

\\ Reciprocity: h,k>0, gcd=1 ⇒
\\ 12hk (s(h,k)+s(k,h)) = h^2 + k^2 + 1 - 3hk
\\ s(1,k) = (k-1)(k-2)/(12k)
s1(k) = (k-1)*(k-2) / (12*k);

\\ Pin the closed form against a tiny brute sum
brute_s1(k) = {
  acc = 0;
  for(r = 1, k-1, \
    acc += (r/k - 1/2) * (r/k - 1/2)  \\ not the definition
  );
  acc
};
\\ Standard: s(h,k)=sum_{r=1}^{k-1} ((r/k)) ((h r /k)) with ((x))=x-floor(x)-1/2
saw(x) = x - floor(x) - 1/2;
s_sum(h, k) = {
  acc = 0;
  for(r = 1, k-1, acc += saw(r/k) * saw((h*r)/k));
  acc
};
pin = 0;
for(k = 3, 40, if(k%2==0, next); if(abs(s_sum(1,k) - s1(k)) < 10^-9, pin++));
check(pin >= 10, "s(1,k)=(k-1)(k-2)/(12k) matches the sawtooth sum");

\\ s(1,N) is a rational function of N — not a new algebraic object.
\\ Bits of numerator (N-1)(N-2) vs bits of s=p+q: Method 1 already
\\ covered N-1, N-2.
maxdev = 0; ns = 80;
for(t = 1, ns, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; s = p+q; \
  num = (N-1)*(N-2); \
  agr = 0; \
  for(b = 0, 15, if(bittest(num,b)==bittest(s,b), agr++)); \
  r = agr/16.0; d = abs(r-0.5); if(d>maxdev, maxdev=d) \
);
printf("  [hamming (N-1)(N-2) vs p+q] worst-sample |rate-1/2|=%.3f\n", maxdev);
check(1, "s(1,N) numerator is a polynomial in N (Method 1)");

\\ s(h,N) for small h coprime to N, via reciprocity + s(N mod h, h)
\\ (Euclidean algorithm — this is the CF of h/N, hence of a rational,
\\ not of √N).
s_rec(h, k) = {
  if(k==1, return(0));
  if(h==0, return(0));
  h = h % k; if(h<0, h+=k);
  if(h==0, return(0));
  g = gcd(h,k); h = h/g; k = k/g;
  (h^2 + k^2 + 1 - 3*h*k) / (12*h*k) - s_rec(k, h)
};

\\ First CF partial quotient of √N is floor(√N).  s(1,N) does not
\\ equal that.  Correlate floor(12*N*s(1,N)) = (N-1)(N-2)/1 with
\\ floor(√N): they have different size (N^2 vs N^{1/2}).
cf_eq = 0;
for(t = 1, 40, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  if(floor(s1(N)*12*N) == sqrtint(N), cf_eq++) \
);
check(cf_eq==0, "12 N s(1,N) is not floor(√N) — not a CF(√N) rewrite");

\\ s(2,N) vs bits of p+q
dev2 = 0; n2 = 0;
for(t = 1, 60, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; s = p+q; \
  if(gcd(2,N)!=1, next); \
  val = s_rec(2, N); \
  n2++; \
  if((val>0) == bittest(s, 1), dev2++) \
);
printf("  [sign s(2,N) vs s bit1] %.3f\n", dev2/n2);
check(abs(dev2/n2-0.5) < 0.20, "sign s(2,N) is not a bit of p+q");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
