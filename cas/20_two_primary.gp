\\ CAS witnesses — 2-primary structure of (Z/NZ)*.
\\ Mirrors TwoPrimary.v.  Heights, mismatch rates, Blum vs deep-matched.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

v2(n) = valuation(n, 2);

height(a, p) = {
  s = v2(p-1); t = (p-1)/2^s;
  g = lift(Mod(a,p)^t);
  k = 0;
  while(g != 1, g = lift(Mod(g,p)^2); k++);
  k
};

\\ cyclic-model frequencies: P(v2(ord)=0) = 2^{-s},
\\ P(v2(ord)=i) = 2^{i-1-s} for i=1..s.
pcyclic(s, i) = if(i==0, 1/2^s, if(i>=1 && i<=s, 2^(i-1-s), 0));
pmatch(sp, sq) = {
  m = 0;
  for(i = 0, min(sp,sq), m += pcyclic(sp,i)*pcyclic(sq,i));
  m
};

\\ valuations of p-1
check(v2(11-1) == 1,                    "v2(10)=1  (11≡3 mod 4, Blum)");
check(v2(17-1) == 4,                    "v2(16)=4  (17≡1 mod 16)");
check(v2(13-1) == 2,                    "v2(12)=2  (13≡5 mod 8)");
check(v2(41-1) == 3,                    "v2(40)=3  (41≡1 mod 8)");
check(v2(lcm(10,16)) == 4,              "v2(λ(11*17))=max(1,4)=4");

\\ four square roots of 1 on 187
N = 187; p = 11; q = 17;
rts = [];
for(x = 0, N-1, if(lift(Mod(x,N)^2)==1, rts = concat(rts, [x])));
check(#rts == 4,                        "exactly four square roots of 1");
check(setintersect(Set(rts), Set([1, N-1])) == Set([1, N-1]), "±1 are among them");
mixed = [];
for(i = 1, #rts, if(rts[i]!=1 && rts[i]!=N-1, mixed = concat(mixed, [rts[i]])));
check(#mixed == 2,                      "two mixed CRT roots");
check(gcd(mixed[1]-1, N)==p || gcd(mixed[1]-1, N)==q, "a mixed root splits N");

\\ textbook RSA: heights of a=2
check(height(2,11) == 1,                "2-height of 2 mod 11 is 1");
check(height(2,17) == 3,                "2-height of 2 mod 17 is 3 (ord=8)");
check(height(2,11) != height(2,17),     "mismatch ⇒ Miller splits 187");

\\ exhaustive mismatch on N=187, units in 1..N-1
mis = 0; tot = 0; matchpm1 = 0;
for(a = 1, N-1, \
  if(gcd(a,N)==1, \
    tot++; \
    hp = height(a,p); hq = height(a,q); \
    if(hp != hq, mis++); \
    if((a==1 || a==N-1) && hp==hq, matchpm1++) \
  ) \
);
check(tot == eulerphi(N),               "φ(187) units");
check(mis == 150,                       "150 / 160 units mismatch (formula 15/16)");
check(matchpm1 == 2,                    "±1 are the two height-matches at the extremes");
printf("  [2adic] 11×17 v2=(1,4): mismatch %d/%d  cyclic-model %d/%d\n", \
  mis, tot, 15*tot/16, tot);

\\ Blum pair 11×19 (both v2=1): formula says 1/2
p2 = 11; q2 = 19; N2 = p2*q2;
check(v2(p2-1)==1 && v2(q2-1)==1,       "11,19 both Blum");
mis2 = 0; tot2 = 0;
for(a = 1, N2-1, \
  if(gcd(a,N2)==1, \
    tot2++; \
    if(height(a,p2) != height(a,q2), mis2++) \
  ) \
);
check(2*mis2 == tot2,                   "Blum (1,1): mismatch is exactly 1/2");
printf("  [2adic] 11×19 v2=(1,1): mismatch %d/%d\n", mis2, tot2);

\\ matched-deep: 17 and 97, v2(16)=4, v2(96)=5 — close
\\ 17 (v2=4) and 257 (v2=8) 
\\ pair with equal v2=3: 41 (v2=3) and 73 (72=8*9, v2=3)
p3 = 41; q3 = 73;
check(v2(p3-1)==3 && v2(q3-1)==3,       "41,73 matched v2=3");
N3 = p3*q3;
mis3 = 0; tot3 = 0;
for(a = 1, N3-1, \
  if(gcd(a,N3)==1, \
    tot3++; \
    if(height(a,p3) != height(a,q3), mis3++) \
  ) \
);
pred3 = 1 - pmatch(3,3);
\\ pmatch(3,3) = 2^{-3}*2^{-3} + 2^{-3}*2^{-3} + 2^{-2}*2^{-2} + 2^{-1}*2^{-1}
\\ = 1/64 + 1/64 + 1/16 + 1/4 = 2/64 + 4/64 + 16/64 = 22/64 = 11/32
\\ mismatch = 21/32 = 0.656
check(abs(mis3/tot3 - pred3) < 0.001,   "matched v2=3: exhaustive matches cyclic formula");
printf("  [2adic] 41×73 v2=(3,3): mismatch %d/%d  formula %.4f\n", \
  mis3, tot3, pred3);

\\ Williams pair 11×23: both v2=1, same 1/2 as any Blum pair
check(v2(23-1)==1,                      "23 is Blum (Williams q)");
check(11%8==3 && 23%8==7,               "Williams shape ⇒ Blum 2-adic (1,1)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
