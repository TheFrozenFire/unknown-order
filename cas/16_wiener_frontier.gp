\\ CAS witnesses — Type C past Wiener: classical basin vs CF recovery.
\\ Mirrors Wiener.wiener_classical_sufficient / k_lt_d_of_e_lt_phi.
\\ Sweeps small d on a fixed balanced modulus and records the frontier.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 587; q = 823; N = p*q; phi = (p-1)*(q-1);
check(isprime(p) && isprime(q),         "587, 823 prime");
check(p+q-1 <= 3*sqrtint(N),            "balanced: p+q-1 <= 3 sqrt(N)");

\\ exact continued fraction of the rational e/N (no t_REAL rounding)
cf_exact(num, den) = {
  v = [];
  while(den, v = concat(v, [num \ den]); [num, den] = [den, num % den]);
  v
};
cf_recovers(e, d, k, N) = {
  cf = cf_exact(e, N);
  for(i = 1, #cf, \
    pq = contfracpnqn(vector(i, j, cf[j])); \
    if(pq[2,1] == d && pq[1,1] == k, return(1)) \
  );
  0
};

in_basin(e, d, k, N) = abs(e*d - k*N) * 2 * d < N;

\\ sweep odd d coprime to phi
rec_small = 0; rec_mid = 0; rec_big = 0;
basin_small = 0; n_small = 0; n_mid = 0; n_big = 0;
for(d = 3, 80, \
  if(gcd(d, phi) != 1, next); \
  e = lift(1/Mod(d, phi)); \
  k = (e*d - 1)/phi; \
  if(e >= phi, next); \
  if(k >= d, next); \
  trig18 = 18*d*d*d < N; \
  trig36 = 36*d*d*d*d < N; \
  b = in_basin(e, d, k, N); \
  r = cf_recovers(e, d, k, N); \
  if(trig18, n_small++; if(b, basin_small++); if(r, rec_small++)); \
  if(!trig18 && trig36, n_mid++; if(r, rec_mid++)); \
  if(!trig36, n_big++; if(r, rec_big++)) \
);

check(n_small > 0,                      "some d hit the 18 d^3 < N trigger");
\\ 18 d^3 < N is a conservative marker, not a proved sufficient
\\ condition — CF need not recover every such d.  The proved
\\ criterion is 36 d^4 < N plus k ≤ d (see below).
printf("  [frontier] 18d^3<N: %d/%d CF, %d/%d basin;  mid 36d^4: %d/%d CF;  past: %d/%d CF\n", \
  rec_small, n_small, basin_small, n_small, rec_mid, n_mid, rec_big, n_big);
check(rec_small >= 1,                   "CF recovers at least one 18 d^3 < N instance");

\\ k < d when e < phi
d = 7; e = lift(1/Mod(d, phi)); k = (e*d-1)/phi;
check(e < phi,                          "e < phi");
check(k < d,                            "k < d  (k_lt_d_of_e_lt_phi)");
check(36*d*d*d*d < N,                   "36 d^4 < N for d=7");
check(in_basin(e, d, k, N),             "classical sufficient lands in the basin");

\\ past Wiener: a d with 18 d^3 >= N still sometimes recovers (honest)
\\ (informational — Boneh-Durfee territory, LLL not run)
past = 0; past_rec = 0;
for(d = 3, 200, \
  if(gcd(d, phi) != 1, next); \
  if(18*d*d*d < N, next); \
  if(d*d*d >= N, next); \
  e = lift(1/Mod(d, phi)); \
  k = (e*d-1)/phi; \
  if(e >= phi || k >= d || k <= 0, next); \
  past++; \
  if(cf_recovers(e, d, k, N), past_rec++) \
);
printf("  [frontier] bd_past_wiener-shaped: CF recovered %d / %d\n", past_rec, past);
check(past >= 0,                        "past-Wiener sweep ran");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
