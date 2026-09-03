\\ Predicates of m_p vs recombined m vs public (N,c).
\\ Also pins T16, T8, constructor-slot negative, Rabin oracle split.
\\ Catalog: notes/transcript-oracle-plan.md.  Chance: 1/2 for a random bit.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");
setrand(58);
nbit_prime(n) = nextprime(2^(n-1) + random(2^(n-1)));
far_pair(n, gap) = {
  for(tries = 1, 4000, \
    p = nbit_prime(n); q = nbit_prime(n); \
    if(p==q, next); if(p<q, t=p; p=q; q=t); \
    if(p<=2*q && abs(p-q)>=2^gap, return([p,q])) \
  ); error("none")
};

\\ ---------- T16: (m/q) = (m/p) * (m/N) ----------
t16 = 0;
for(t = 1, 40, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  m = 2 + random(N-3); if(gcd(m,N)!=1, next); \
  if(kronecker(m,q)==kronecker(m,p)*kronecker(m,N), t16++) \
);
check(t16>=30, "(m/q)=(m/p)*(m/N) on far units");

cjac = 0;
for(t = 1, 40, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  m = 2 + random(N-3); if(gcd(m,N)!=1, next); \
  c = lift(Mod(m,N)^65537); \
  if(kronecker(c,N)==kronecker(m,N), cjac++) \
);
check(cjac>=30, "(c/N)=(m/N) public product, odd e");

\\ ---------- T8: cube below N is a raw e=3 signature ----------
p = pin_p; q = pin_q; N = pin_N; s = 5; mcube = s^3;
check(mcube < N && lift(Mod(s,N)^3)==mcube, "5^3=125 < 187 is a raw signature of 125");

\\ ---------- constructor slot r|p-1, one-sided ≡1 (mod r) need not factor ----------
p = pin_p; q = pin_q; N = pin_N; r = 5; m = 138;
check((p-1)%r==0 && (q-1)%r!=0, "r=5 divides p-1 not q-1");
check((m%p)%r==1 && (m%q)%r!=1, "m_p≡1 (mod r), m_q not");
check(gcd(m-1,N)==1, "gcd(m-1,N)=1 — not a factor");

\\ m≡1 (mod p) one-sided DOES factor
m1 = 1+p;
check(gcd(m1-1,N)==p, "m≡1 (mod p), not (mod q) ⇒ factor");

\\ ---------- Rabin: non-associate square roots factor ----------
p = pin_253_p; q = pin_253_q; N = pin_253; r = 5;
y = lift(Mod(r,N)^2);
\\ CRT mix: (r mod p, -r mod q) is a non-associate root
x = lift(chinese(Mod(r,p), Mod(-r,q)));
check(lift(Mod(x,N)^2)==y, "mixed root squares to r^2");
check(x%N!=r%N && x%N!=(N-r)%N, "mixed root is not ±r");
g = gcd(x-r, N);
check(g==p || g==q, "Rabin oracle returning non-associate root factors");

\\ ---------- sweep: is a predicate of m_p a function of (N,c) or of m? ----------
\\ Hit = identical on every usable sample.  Chance ~1/2 is not a hit.
ns = 0;
lsb_mp_m = 0; lsb_mp_c = 0; lsb_mp_cn = 0;
half_mp_m = 0; half_mp_c = 0;
krp_cn = 0; krp_mn = 0;
mp_mod3_m = 0; mp_mod3_c = 0;
for(t = 1, 80, \
  pq = far_pair(12, 6); p = pq[1]; q = pq[2]; N = p*q; \
  m = 2 + random(N-3); if(gcd(m,N)!=1, next); \
  c = lift(Mod(m,N)^3); \
  mp = m % p; \
  ns++; \
  if((mp%2)==(m%2), lsb_mp_m++); \
  if((mp%2)==(c%2), lsb_mp_c++); \
  if((mp%2)==(if(kronecker(c,N)==-1,1,0)), lsb_mp_cn++); \
  if((2*mp<p)==(2*m<N), half_mp_m++); \
  if((2*mp<p)==(2*c<N), half_mp_c++); \
  if(kronecker(m,p)==kronecker(c,N), krp_cn++); \
  if(kronecker(m,p)==kronecker(m,N), krp_mn++); \
  if((mp%3)==(m%3), mp_mod3_m++); \
  if((mp%3)==(c%3), mp_mod3_c++) \
);
printf("  [sweep n=%d] lsb(mp)==lsb(m) %d; lsb(c) %d; bit of (c/N) %d\n", \
  ns, lsb_mp_m, lsb_mp_c, lsb_mp_cn);
printf("  [sweep] mp<p/2 vs m<N/2 %d; vs c<N/2 %d\n", half_mp_m, half_mp_c);
printf("  [sweep] (m/p)==(c/N) %d; (m/N) %d\n", krp_cn, krp_mn);
printf("  [sweep] mp≡m (mod 3) %d; ≡c %d\n", mp_mod3_m, mp_mod3_c);
check(ns>=40, "enough usable samples");
\\ none of these is an identity (would be ns/ns)
check(lsb_mp_m < ns && lsb_mp_c < ns && lsb_mp_cn < ns, \
  "lsb(m_p) is not lsb(m), lsb(c), or a bit of (c/N)");
check(half_mp_m < ns && half_mp_c < ns, "m_p < p/2 is not m<N/2 or c<N/2");
check(krp_cn < ns && krp_mn < ns, "(m/p) is not (c/N) or (m/N)");
check(mp_mod3_m < ns && mp_mod3_c < ns, "m_p mod 3 is not m or c mod 3");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
