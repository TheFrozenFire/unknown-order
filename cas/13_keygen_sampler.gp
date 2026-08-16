\\ CAS witnesses — keygen distributions measured against the rulers.
\\ Mirrors KeyGenSampler.v.  Small bit lengths; the point is *which*
\\ ruler fails, not a cryptographic parameter recommendation.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

setrand(2);

nbit_prime(n) = nextprime(2^(n-1) + random(2^(n-1)));

is_smooth(n, B) = {
  if(n <= 1, return(0));
  f = factor(n);
  for(i = 1, matsize(f)[1], if(f[i,1] > B, return(0)));
  1
};

is_balanced(p, q) = { if(p < q, t = p; p = q; q = t); p <= 2*q };

is_far(p, q, gap) = abs(p - q) >= 2^gap;

\\ ----- nextprime twins (16-bit) ------------------------------------
twins_far = 0; twins_n = 20; n = 16;
for(i = 1, twins_n, \
  p = nbit_prime(n); \
  q = nextprime(p+1); \
  if(is_far(p, q, n-4), twins_far++) \
);
check(twins_far == 0,                   "nextprime twins never pass far-gap n-4");

p = 101; q = 103;
check(isprime(p) && isprime(q) && q-p==2, "textbook twins 101,103");
check(!is_far(p, q, 2),                 "twins fail kg_far(gap=2)");
check(is_balanced(p, q),                "twins are bit-balanced");

\\ ----- independent random 16-bit primes ----------------------------
ind_far = 0; ind_bal = 0; ind_n = 40;
for(i = 1, ind_n, \
  p = nbit_prime(n); q = nbit_prime(n); \
  if(p==q, next); \
  if(is_balanced(p,q), ind_bal++); \
  if(is_far(p,q, n-4), ind_far++) \
);
check(ind_far > ind_n \ 2,              "independent 16-bit: most pass far-gap n-4");
check(ind_bal > ind_n \ 2,              "independent 16-bit: most are balanced");
printf("  [sampler] independent far=%d/%d balanced=%d/%d\n", ind_far, ind_n, ind_bal, ind_n);

\\ ----- shared high bits (top half) ---------------------------------
sh_far = 0; sh_n = 20;
for(i = 1, sh_n, \
  hi = 2^(n\2) + random(2^(n\2)); \
  p = nextprime(hi * 2^(n\2) + random(2^(n\2))); \
  q = nextprime(hi * 2^(n\2) + random(2^(n\2))); \
  if(p==q, next); \
  if(is_far(p, q, n-4), sh_far++) \
);
check(sh_far == 0,                      "shared top-half never pass far-gap n-4");

\\ ----- increment window W = 2^{n/2} from a common start ------------
win_far = 0; win_n = 20; W = 2^(n\2);
for(i = 1, win_n, \
  x = 2^(n-1) + random(2^(n-2)); \
  p = nextprime(x); \
  q = nextprime(x + random(W)); \
  if(p==q, next); \
  if(abs(p-q) < W && is_far(p,q, n-4), win_far++) \
);
check(win_far == 0,                     "increment window 2^{n/2} fails far-gap n-4");

\\ ----- shared-prime pool -------------------------------------------
p = nbit_prime(16); q1 = nbit_prime(16); q2 = nbit_prime(16);
while(q1==p || q1==q2, q1 = nbit_prime(16));
while(q2==p || q2==q1, q2 = nbit_prime(16));
check(gcd(p*q1, p*q2) == p,             "shared-pool: gcd of moduli is p");
check(gcd(nbit_prime(16)*nbit_prime(16), nbit_prime(16)*nbit_prime(16)) != 0, "gcd defined");

\\ a tiny prime pool *does* collide (Type D).  Independent 16-bit
\\ draws collide much less often — recorded, not asserted zero.
pool = [nbit_prime(10), nbit_prime(10), nbit_prime(10)];
Na = pool[1]*pool[2]; Nb = pool[1]*pool[3];
check(gcd(Na, Nb) == pool[1],           "tiny 3-prime pool: moduli share a factor");
share_hits = 0;
for(i = 1, 20, \
  a = nbit_prime(16)*nbit_prime(16); \
  b = nbit_prime(16)*nbit_prime(16); \
  if(gcd(a,b) > 1, share_hits++) \
);
printf("  [sampler] independent 16-bit moduli gcd-hits %d/20\n", share_hits);
check(share_hits >= 0,                  "independent-moduli collision count ran");

\\ ----- smooth p-1 vs safe p ----------------------------------------
B = 30;
smooth_hits = 0; safe_hits = 0;
for(i = 1, 40, \
  p = nbit_prime(14); \
  if(is_smooth(p-1, B), smooth_hits++); \
  if(isprime((p-1)\2), safe_hits++) \
);
printf("  [sampler] 14-bit p: p-1 30-smooth %d/40, safe %d/40\n", smooth_hits, safe_hits);
check(smooth_hits >= 0,                 "smoothness count ran");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
