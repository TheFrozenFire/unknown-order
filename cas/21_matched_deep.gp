\\ CAS witnesses — is kg_2adic_matched_deep a live generation defect?
\\ Mirrors KeyGenSampler + TwoPrimary rulers.  Small bit lengths;
\\ the point is *which* sampler produces deep matching 2-valuations,
\\ not a cryptographic parameter recommendation.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

setrand(3);

nbit_prime(n) = nextprime(2^(n-1) + random(2^(n-1)));

v2(n) = valuation(n, 2);

both_deep(p, q, d) = v2(p-1) >= d && v2(q-1) >= d;
matched_deep(p, q, d) = v2(p-1) == v2(q-1) && v2(p-1) >= d;

\\ Heuristic for a random odd prime: P(v2(p-1) >= d) = 2^{1-d} (d>=1).
\\ P(both_deep d) = 2^{2-2d}.  P(matched_deep d) = sum_{k>=d} 2^{-2k}
\\ = (4/3) * 2^{-2d} for d>=1.

pred_both(d) = 2.^(2-2*d);
pred_matched(d) = (4/3) * 2.^(-2*d);

\\ ----- independent 24-bit primes -----------------------------------
n = 24; trials = 200;
ind_both2 = 0; ind_both3 = 0; ind_both4 = 0;
ind_match2 = 0; ind_match3 = 0; ind_match4 = 0;
for(i = 1, trials, \
  p = nbit_prime(n); q = nbit_prime(n); \
  while(p==q, q = nbit_prime(n)); \
  if(both_deep(p,q,2), ind_both2++); \
  if(both_deep(p,q,3), ind_both3++); \
  if(both_deep(p,q,4), ind_both4++); \
  if(matched_deep(p,q,2), ind_match2++); \
  if(matched_deep(p,q,3), ind_match3++); \
  if(matched_deep(p,q,4), ind_match4++) \
);
\\ independent should sit near the heuristic (loose bands)
check(abs(ind_both2/trials - pred_both(2)) < 0.12, "independent: both>=2 near 1/4");
check(abs(ind_both3/trials - pred_both(3)) < 0.10, "independent: both>=3 near 1/16");
check(ind_match3/trials < 0.08,                   "independent: matched>=3 is rare (<8%)");
printf("  [indep] both>=2 %d/%d  both>=3 %d/%d  both>=4 %d/%d\n", \
  ind_both2, trials, ind_both3, trials, ind_both4, trials);
printf("  [indep] match>=2 %d/%d  match>=3 %d/%d  match>=4 %d/%d\n", \
  ind_match2, trials, ind_match3, trials, ind_match4, trials);
printf("  [indep] heuristic both  %.3f/%.3f/%.3f  match %.3f/%.3f/%.3f\n", \
  pred_both(2), pred_both(3), pred_both(4), \
  pred_matched(2), pred_matched(3), pred_matched(4));

\\ ----- nextprime twins ---------------------------------------------
tw_both3 = 0; tw_match3 = 0; tw_same = 0;
for(i = 1, trials, \
  p = nbit_prime(n); q = nextprime(p+1); \
  if(both_deep(p,q,3), tw_both3++); \
  if(matched_deep(p,q,3), tw_match3++); \
  if(v2(p-1)==v2(q-1), tw_same++) \
);
\\ nextprime does *not* force deep matching: consecutive odd numbers
\\ have opposite residues mod 4, so one is Blum (v2=1) more often.
check(tw_both3 <= ind_both3 + 8, "nextprime does not inflate both>=3 vs independent");
printf("  [twin]  both>=3 %d/%d  match>=3 %d/%d  equal-v2 %d/%d\n", \
  tw_both3, trials, tw_match3, trials, tw_same, trials);

\\ ----- forced p ≡ q ≡ 1 (mod 2^d) ---------------------------------
\\ This *is* the live defect: a generator that samples both primes
\\ from the 1 (mod 2^d) progression.
dforce = 4;
\\ Walk the progression 1 (mod 2^d).  nextprime leaves it.
next_1mod(bits, d) = {
  x = 2^d * (2^(bits-d-1) + random(2^(bits-d-1))) + 1;
  while(!isprime(x), x += 2^d);
  x
};
forced_ok = 0;
for(i = 1, 40, \
  p = next_1mod(n, dforce); q = next_1mod(n, dforce); \
  while(p==q, q = next_1mod(n, dforce)); \
  if(p % 2^dforce == 1 && q % 2^dforce == 1 && both_deep(p,q,dforce), \
    forced_ok++) \
);
check(forced_ok == 40, "forced 1 (mod 16): every pair is both_deep 4");
printf("  [force] 1 (mod 2^%d): %d/40 pairs both_deep\n", dforce, forced_ok);

\\ ----- safe primes are the opposite choice (Blum, v2=1) -----------
\\ p = 2r+1 with r prime ⇒ p ≡ 3 (mod 4) ⇒ v2(p-1)=1.
safe_blum = 0; safe_n = 0;
r = 10007;
while(safe_n < 15, \
  r = nextprime(r+1); \
  p = 2*r + 1; \
  if(isprime(p), \
    safe_n++; \
    if(v2(p-1)==1, safe_blum++) \
  ) \
);
check(safe_blum == safe_n, "safe primes are Blum: v2(p-1)=1 always");
printf("  [safe]  %d/%d safe primes have v2=1 (Blum, not matched-deep)\n", \
  safe_blum, safe_n);

\\ a forced pair is Miller-hostile; a safe pair is Miller-friendly
p = 17; q = 97;
check(v2(16)>=4 && v2(96)>=5,           "17,97 sit at deep unmatched 2-parts");
check(v2(10)==1 && v2(18)==1,           "11,19 are Blum (1,1)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
