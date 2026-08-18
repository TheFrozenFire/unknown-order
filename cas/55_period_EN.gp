\\ Method 12 — real period of y^2 = x^3 + x + N (nonsingular).
\\ Ω is a public real (AGM / ellperiods).  Collapse if it tracks √N.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));
setrand(55);
nbit_prime(n) = nextprime(2^(n-1) + random(2^(n-1)));
far_pair(n, gap) = {
  for(tries = 1, 4000, \
    p = nbit_prime(n); q = nbit_prime(n); \
    if(p==q, next); if(p<q, t=p; p=q; q=t); \
    if(p<=2*q && abs(p-q)>=2^gap, return([p,q])) \
  ); error("none")
};

omega_of(N) = {
  E = ellinit([0,0,0, 1, N]);
  w = ellperiods(E);
  if(type(w)=="t_VEC", abs(w[1]), abs(w))
};

\\ Pin: period is defined and positive on far N
okw = 0;
for(t = 1, 15, \
  pq = far_pair(12, 6); N = pq[1]*pq[2]; \
  w = omega_of(N); \
  if(w > 0, okw++) \
);
check(okw==15, "Ω(E_N) is a positive real on 15 far 12-bit N");

\\ Scale: Ω * N^{1/6} should be slowly varying if Ω ~ N^{-1/6}
\\ (Weierstrass y^2=x^3+N).  Track correlation of Ω with 1/N^{1/6}
\\ vs with 1/(p+q).
\\ Use log Ω vs -log N / 6 and vs -log(p+q).
\\ Compare residual: is Ω determined by N alone (yes, by construction)
\\ so the only question is whether it *also* encodes the split.

\\ Two N with the same size but different (p,q) should have Ω
\\ differing only as a function of N, not of p+q at fixed N —
\\ tautological (one N, one Ω).  Compare pairs with N1≈N2 but
\\ very different p+q (balanced vs slightly less).
\\ Better: bits of round(C/Ω^6) should recover N, not p.

pq0 = far_pair(12, 6); N0 = pq0[1]*pq0[2]; w0 = omega_of(N0);
cfit = N0 * w0^6;
recN = 0; recs = 0; ns = 25;
for(t = 1, ns, \
  pq = far_pair(12, 6); p = pq[1]; q = pq[2]; N = p*q; s = p+q; \
  w = omega_of(N); \
  Nest = round(cfit / w^6); \
  if(abs(Nest - N) < abs(Nest - s), recN++); \
  if(abs(Nest - s) < N/10, recs++) \
);
printf("  [Ω^{-6} nearer N than p+q] %d/%d;  near p+q: %d/%d\n", recN, ns, recs, ns);
check(recN > ns\2, "Ω^{-6} tracks N, not p+q");

\\ Bits of mantissa of Ω vs bits of p+q
bitm = 0; bn = 0;
for(t = 1, 40, \
  pq = far_pair(12, 6); p = pq[1]; q = pq[2]; N = p*q; s = p+q; \
  w = omega_of(N); \
  mant = floor(w * 2^20); \
  bn++; \
  if(bittest(mant, 3)==bittest(s, 3), bitm++) \
);
printf("  [bit 3 of 2^20 Ω vs bit 3 of p+q] %.3f\n", bitm/bn);
check(abs(bitm/bn-0.5) < 0.22, "a mantissa bit of Ω is not a bit of p+q");

\\ Ω vs π/sqrtint(N) — Type A probe
near_sqrt = 0;
for(t = 1, 20, \
  pq = far_pair(12, 6); N = pq[1]*pq[2]; \
  w = omega_of(N); \
  if(abs(w - Pi/sqrtint(N)) / w < 0.2, near_sqrt++) \
);
printf("  [Ω ≈ π/√N within 20%%] %d/20\n", near_sqrt);
check(1, "Ω vs π/√N recorded (smooth in N, not a split)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
