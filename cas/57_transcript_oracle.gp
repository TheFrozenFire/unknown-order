\\ Transcript / oracle algebra (notes/transcript-oracle-plan.md).
\\ Mirrors TranscriptOracle.v.  Not a TLS padding-oracle.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");
setrand(57);
nbit_prime(n) = nextprime(2^(n-1) + random(2^(n-1)));
far_pair(n, gap) = {
  for(tries = 1, 4000, \
    p = nbit_prime(n); q = nbit_prime(n); \
    if(p==q, next); if(p<q, t=p; p=q; q=t); \
    if(p<=2*q && abs(p-q)>=2^gap, return([p,q])) \
  ); error("none")
};

\\ ---------- T5: (c/N)=(m/N) for odd e ----------
p = pin_p; q = pin_q; N = pin_N; e = 3; d = 27;
m = 42; c = lift(Mod(m,N)^e);
check(kronecker(c,N)==kronecker(m,N), "(c/N)=(m/N) on rsa_test");
kr = 0;
for(t = 1, 40, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  m = 2 + random(N-3); if(gcd(m,N)!=1, next); \
  c = lift(Mod(m,N)^65537); \
  if(kronecker(c,N)==kronecker(m,N) && kronecker(c,p)==kronecker(m,p), kr++) \
);
check(kr>=35, "(c/N)=(m/N) on far 16-bit pairs, e=65537");

\\ ---------- T24 / T25: homomorphism and blinding ----------
p = pin_p; q = pin_q; N = pin_N; e = 3; d = 27;
m1 = 4; m2 = 9;
s1 = lift(Mod(m1,N)^d); s2 = lift(Mod(m2,N)^d);
check(lift(Mod(m1*m2,N)^d)==(s1*s2)%N, "sign homomorphism");
check(lift(Mod(N-1,N)^d)==N-1, "sign(-1)=-1 for odd d");
c = lift(Mod(42,N)^e); r = 5;
check(lift(Mod((c*lift(Mod(r,N)^e))%N,N)^d)==(lift(Mod(c,N)^d)*r)%N, "decrypt blinding");

\\ ---------- T12: lsb(2m mod N) is the half bit ----------
halfok = 0;
for(t = 1, 80, \
  N = 2*(50+random(200))+1; m = random(N); \
  bit = ((2*m)%N)%2; \
  if((bit==0) == (2*m < N), halfok++) \
);
check(halfok==80, "lsb(2m mod N)=0 iff m < N/2 on 80 odd N");

\\ ---------- T11: interval-halving recovers m ----------
recover(m, k) = {
  lo = 0; hi = 2^k;
  for(i = 1, k, \
    mid = (lo+hi)\2; \
    if(m < mid, hi = mid, lo = mid) \
  );
  lo
};
recok = 0;
for(t = 1, 40, \
  k = 12; m = random(2^k); \
  if(recover(m,k)==m, recok++) \
);
check(recok==40, "comparison-oracle binary search recovers m");

\\ ---------- T29: Bellcore ----------
p = pin_p; q = pin_q; N = pin_N; e = 3; d = 27; m = 42;
sig_good = lift(Mod(m,N)^d);
sig_p = lift(Mod(sig_good, p));
sig_bad = lift(chinese(Mod(sig_p,p), Mod(3,q)));
g = gcd(lift(Mod(sig_bad,N)^e)-m, N);
check(g==p || g==q, "Bellcore gcd(σ_bad^e - m, N) is a prime factor");
check(lift(Mod(sig_bad,p)^e)==m%p, "faulty sig still correct mod p");
check(lift(Mod(sig_bad,q)^e)!=m%q, "faulty sig wrong mod q");

\\ ---------- T4: common modulus ----------
e1 = 3; e2 = 5; a = 2; k = 1;
check(e1*a == 1+e2*k, "3*2 = 1+5*1");
m = 42; N = pin_N;
c1 = lift(Mod(m,N)^e1); c2 = lift(Mod(m,N)^e2);
w = lift(1/Mod(lift(Mod(c2,N)^k), N));
check((lift(Mod(c1,N)^a)*w)%N == m%N, "common-modulus recovers m");

\\ ---------- K1: one-sided congruence ----------
p = pin_p; q = pin_q; N = pin_N; mm = 1+p;
check(gcd(mm-1, N)==p, "m≡1 (mod p), m≢1 (mod q) ⇒ gcd(m-1,N)=p");

\\ ---------- K5: Williams (2/p) is shape, not N mod 8 ----------
check(pin_253_p%8==3 && pin_253_q%8==7 && pin_253%8==5, "Williams pair N≡5 (mod 8)");
check(kronecker(2,pin_253_p)==-1 && kronecker(2,pin_253_q)==1, "Williams (2/p),(2/q)");
check((5*17)%8==5 && 5%8==5 && 17%8==1, "5·17≡5 (mod 8) is not Williams");
check(kronecker(2,5)==-1 && kronecker(2,17)==1, "non-Williams two-chars");

\\ ---------- T10: wrap interval; PKCS#1 v1.5 is [2B, 3B) ----------
r = 3; mm = 5; N = 11; B = 5;
rem = (r*mm) % N;
check(rem < B, "residue in [0, B)");
kk = (r*mm) \ N;
check(kk*N <= r*mm && r*mm < kk*N + B, "k N ≤ r m < k N + B");
BB = 256;
rest = 100;
check(2*BB <= 2*BB + rest && 2*BB + rest < 3*BB, "PKCS#1 type-2 in [2B, 3B)");
check(0 <= 50 && 50 < BB, "Manger interval [0, B)");
check(!(2*BB <= 50 && 50 < 3*BB), "Manger cut is not type-2");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));

