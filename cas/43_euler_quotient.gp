\\ Method 2 — Euler quotient.  Public group element a^{N+1} ≡ a^{p+q} (mod N).
\\ Identity pin + cheap bit-extraction battery on honest kg_far pairs.
\\ Chance: fair bit match is 1/2.  With 400 samples, 4σ ≈ 0.10.
\\ Look-elsewhere over ~200 cells: fail only if |rate-1/2| >= 0.16.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

setrand(43);

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

powN(a, N) = lift(Mod(a, N)^(N+1));
powS(a, s, N) = lift(Mod(a, N)^s);

\\ ---------- 1. Identity ----------
p = pin_p; q = pin_q; N = pin_N; s = p+q;
id_fail = 0;
for(a = -N-3, 2*N+3, if(powN(a,N) != powS(a,s,N), id_fail++));
check(id_fail == 0, "a^{N+1} ≡ a^{p+q} (mod 187) for a in [-190,377]");

pred_fail = 0;
for(a = -N-3, 2*N+3, \
  if(lift(Mod(a,N)^(N-1)) != lift(Mod(a,N)^(s-2)), pred_fail++) \
);
check(pred_fail == 0, "a^{N-1} ≡ a^{p+q-2} (mod 187) on the same range");

id2 = 0;
for(t = 1, 40, \
  pq = far_pair(12, 6); pp = pq[1]; qq = pq[2]; NN = pp*qq; ss = pp+qq; \
  for(j = 1, 40, a = random(NN)-NN\2; if(powN(a,NN) != powS(a,ss,NN), id2++)); \
  if(powN(pp,NN) != powS(pp,ss,NN), id2++); \
  if(powN(qq,NN) != powS(qq,ss,NN), id2++); \
  if(powN(0,NN) != powS(0,ss,NN), id2++); \
  if(powN(-1,NN) != powS(-1,ss,NN), id2++) \
);
check(id2 == 0, "identity on 40 random 12-bit far pairs (sampled a, 0, ±1, p, q)");

hom = 0;
pq = far_pair(14, 8); p = pq[1]; q = pq[2]; N = p*q;
for(i = 1, 30, \
  a = 1+random(N-1); b = 1+random(N-1); \
  if(powN((a*b)%N, N) != (powN(a,N)*powN(b,N))%N, hom++) \
);
check(hom == 0, "(ab)^{N+1} ≡ a^{N+1} b^{N+1} — homomorphism, no extra info");

\\ ---------- 2. Bits of s that are functions of N ----------
check((11+17)%2 == 0, "odd+odd ⇒ s even");
check((11*17)%4 == 3 && (11+17)%4 == 0, "N≡3 (mod 4) ⇒ s≡0 (mod 4)");
check((13*17)%4 == 1 && (13+17)%4 == 2, "N≡1 (mod 4) ⇒ s≡2 (mod 4)");

s4_fail = 0;
for(t = 1, 80, \
  pq = far_pair(12, 6); pp = pq[1]; qq = pq[2]; NN = pp*qq; ss = pp+qq; \
  if(NN%4==1 && ss%4!=2, s4_fail++); \
  if(NN%4==3 && ss%4!=0, s4_fail++) \
);
check(s4_fail == 0, "s mod 4 is a function of N mod 4 (80 far pairs)");

\\ Among N-ambiguous (mod 8) samples, does g(2) mod 32 pin s mod 8?
\\ Count, for each g2%32 bucket with >=8 hits, the most common s%8 share.
cntg = vector(32); cntgs = matrix(32, 8);
amb_n = 0;
for(t = 1, 300, \
  pq = far_pair(14, 8); pp = pq[1]; qq = pq[2]; NN = pp*qq; ss = pp+qq; \
  Nm8 = NN%8; \
  if(Nm8!=1 && Nm8!=5, next); \
  amb_n++; \
  gbin = powN(2,NN)%32; \
  if(gbin<0, gbin = gbin+32); \
  sm = ss%8; \
  cntg[gbin+1] = cntg[gbin+1]+1; \
  cntgs[gbin+1, sm+1] = cntgs[gbin+1, sm+1]+1 \
);
maxp = 0;
for(gbin = 1, 32, \
  if(cntg[gbin] < 8, next); \
  for(sm = 1, 8, \
    pr = cntgs[gbin,sm] / cntg[gbin]; \
    if(pr > maxp, maxp = pr) \
  ) \
);
printf("  [s mod 8 | g2%%32] amb_n=%d max cell rate=%.3f (chance ~0.5)\n", amb_n, maxp);
check(maxp < 0.92, "g(2) mod 32 does not pin s mod 8 on N-ambiguous samples");

\\ ---------- 3. Bit correlation on kg_far ----------
nbit = 16; gap = 10; nsamp = 400;
bases = [2,3,5,6,7,10,11,65537];
nbases = #bases;
nbits_test = 12;
match_s = matrix(nbases, nbits_test);
match_p = matrix(nbases, nbits_test);
match_d = matrix(nbases, nbits_test);
sign_s0 = 0; hw_s0 = 0; gcd_hit = 0; fixpt = 0; fixtry = 0;

for(t = 1, nsamp, \
  pq = far_pair(nbit, gap); \
  pp = pq[1]; qq = pq[2]; NN = pp*qq; ss = pp+qq; dd = abs(pp-qq); \
  for(bi = 1, nbases, \
    a = bases[bi]; g = powN(a, NN); \
    for(bg = 0, nbits_test-1, \
      gb = bittest(g, bg); \
      if(gb == bittest(ss, bg), match_s[bi,bg+1] = match_s[bi,bg+1]+1); \
      if(gb == bittest(pp, bg), match_p[bi,bg+1] = match_p[bi,bg+1]+1); \
      if(gb == bittest(dd, bg), match_d[bi,bg+1] = match_d[bi,bg+1]+1) \
    ) \
  ); \
  g2 = powN(2, NN); \
  if((g2 < NN/2) == bittest(ss, 2), sign_s0++); \
  if(((hammingweight(g2))%2) == bittest(ss, 3), hw_s0++); \
  gg = gcd(g2-1, NN); \
  if(gg>1 && gg<NN, gcd_hit++); \
  for(k = 1, 3, \
    x = 1+random(NN-1); fixtry++; \
    if(powN(x,NN) == x%NN, fixpt++) \
  ) \
);

maxdev = 0; worst = "none";
for(bi = 1, nbases, \
  for(bg = 1, nbits_test, \
    r = match_s[bi,bg]/nsamp; d = abs(r-0.5); \
    if(d > maxdev, maxdev = d; worst = Strprintf("s a=%d bit %d rate=%.3f", bases[bi], bg-1, r)); \
    r = match_p[bi,bg]/nsamp; d = abs(r-0.5); \
    if(d > maxdev, maxdev = d; worst = Strprintf("p a=%d bit %d rate=%.3f", bases[bi], bg-1, r)); \
    r = match_d[bi,bg]/nsamp; d = abs(r-0.5); \
    if(d > maxdev, maxdev = d; worst = Strprintf("d a=%d bit %d rate=%.3f", bases[bi], bg-1, r)) \
  ) \
);
printf("  [bits] n=%d gap=%d samples=%d max |rate-1/2|=%.3f at %s\n", nbit, gap, nsamp, maxdev, worst);
printf("  [bits] sign vs s bit2: %.3f; hw vs s bit3: %.3f\n", sign_s0/nsamp, hw_s0/nsamp);
printf("  [gcd] nontrivial gcd(2^{N+1}-1, N): %d/%d\n", gcd_hit, nsamp);
printf("  [fix] x^{N+1}≡x : %d/%d\n", fixpt, fixtry);
check(maxdev < 0.16, "no bit of g(a) matches a bit of s,p,|p-q| above chance");
check(abs(sign_s0/nsamp-0.5) < 0.16, "sign(g(2)-N/2) is not a bit of s");
check(abs(hw_s0/nsamp-0.5) < 0.16, "Hamming parity of g(2) is not a bit of s");
check(gcd_hit == 0, "gcd(2^{N+1}-1, N) never splits a far modulus");
check(fixpt < fixtry/20, "x^{N+1}≡x is rare (not a counting handle)");

jac_match = 0;
for(t = 1, 200, \
  pq = far_pair(16, 10); pp = pq[1]; qq = pq[2]; NN = pp*qq; ss = pp+qq; \
  j = kronecker(powN(2,NN), NN); \
  if((j==1) == (ss%4==0), jac_match++) \
);
printf("  [jacobi] (g2/N)==+1 vs s≡0 (mod 4): %.3f (s mod 4 already public from N)\n", jac_match/200.0);
check(1, "Jacobi recorded");

\\ ---------- 4. Fermat-in-the-exponent: Type A collapse ----------
close_hit = 0; close_n = 20;
for(t = 1, close_n, \
  pp = nbit_prime(16); qq = nextprime(pp+1); NN = pp*qq; \
  s0 = 2*sqrtint(NN); if(s0%2, s0++); \
  g = powN(2, NN); found = 0; \
  for(k = -2^10, 2^10, \
    if(s0+k < 0, next); \
    if(lift(Mod(2,NN)^(s0+k)) == g, found=1) \
  ); \
  if(found, close_hit++) \
);
printf("  [fermat-exp] close nextprime: recovered k in ±2^10 on %d/%d\n", close_hit, close_n);
check(close_hit > close_n \ 2, "Fermat-in-exponent recovers s on close nextprime (Type A)");

far_hit = 0; far_n = 16;
for(t = 1, far_n, \
  pq = far_pair(24, 20); pp = pq[1]; qq = pq[2]; NN = pp*qq; \
  s0 = 2*sqrtint(NN); if(s0%2, s0++); \
  g = powN(2, NN); found = 0; \
  for(k = -2^12, 2^12, \
    if(s0+k < 0, next); \
    if(lift(Mod(2,NN)^(s0+k)) == g, found=1) \
  ); \
  if(found, far_hit++) \
);
printf("  [fermat-exp] far 24-bit gap=20: recovered k in ±2^12 on %d/%d\n", far_hit, far_n);
check(far_hit == 0, "Fermat-in-exponent fails on kg_far (not a sixth type)");

\\ ---------- 5. Constructible torsion only yields s even ----------
p = pin_p; q = pin_q; N = pin_N;
check(powN(-1, N) == 1, "(-1)^{N+1} ≡ 1");
check((p+q)%2 == 0, "matches (-1)^s for even s");

ematch = 0; e_n = 200;
for(t = 1, e_n, \
  pq = far_pair(16, 10); pp = pq[1]; qq = pq[2]; NN = pp*qq; ss = pp+qq; \
  ge = powN(65537, NN); \
  if(bittest(ge,0) == bittest(ss,1), ematch++) \
);
printf("  [e] bit0(g(65537)) vs bit1(s): %.3f\n", ematch/e_n);
check(abs(ematch/e_n-0.5) < 0.16, "g(65537) bit 0 is not a bit of s");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
