\\ Independent PARI pin of the OSCAR-lab observations.
\\ Not a third confirming tool.  Do not add Julia / OSCAR to cas-gate.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));
setrand(56);
nbit_prime(n) = nextprime(2^(n-1) + random(2^(n-1)));
far_pair(n, gap) = {
  for(tries = 1, 4000, \
    p = nbit_prime(n); q = nbit_prime(n); \
    if(p==q, next); if(p<q, t=p; p=q; q=t); \
    if(p<=2*q && abs(p-q)>=2^gap, return([p,q])) \
  ); error("none")
};

idform(D) = qfbred(Qfb(1, D%2, (D%2 - D)/4));
form_order(f, D) = {
  my(id = idform(D), g = qfbred(f), n = 1);
  while(g != id && n < 200, g = qfbred(g*f); n++);
  n
};

fund(N) = if(N%4==3, -N, -4*N);

rank2(D) = {
  my(G = quadclassunit(D), cyc = G[2], r = 0);
  if(type(cyc)=="t_INT", if(cyc%2==0, r=1), \
    for(i = 1, #cyc, if(cyc[i]%2==0, r++)) \
  );
  r
};

rank4(D) = {
  my(G = quadclassunit(D), cyc = G[2], r = 0);
  if(type(cyc)=="t_INT", if(cyc%4==0, r=1), \
    for(i = 1, #cyc, if(cyc[i]%4==0, r++)) \
  );
  r
};

\\ ---------- 1. (N+1/p) ≡ 1 ----------
kr = 0;
for(t = 1, 40, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  if(kronecker(N+1, p)==1 && kronecker(N+1, q)==1, kr++) \
);
check(kr==40, "(N+1/p)=(N+1/q)=1 on 40 far pairs");

\\ ---------- 2. field 2-rank of fund(-4N) from N mod 4 ----------
r2ok = 0; same_bucket = 0; ns = 30; w = 0; b1 = 0;
for(t = 1, ns, \
  pq = far_pair(12, 6); p = pq[1]; q = pq[2]; N = p*q; \
  D0 = fund(N); \
  r = rank2(D0); \
  want = if(N%4==1, 2, 1); \
  if(r==want, r2ok++); \
  if(N%4==1 && p%4==q%4, same_bucket++); \
  if(p%4==3 && q%4==3, w++); \
  if(p%4==1 && q%4==1, b1++) \
);
printf("  [2-rank fund(-4N)] matches N mod 4: %d/%d; Williams=%d both-1=%d (same public N≡1 bucket)\n", \
  r2ok, ns, w, b1);
check(r2ok==ns, "2-rank of Cl(fund(-4N)) is a function of N mod 4");
check(w>0 && b1>0, "Williams and both-1 both appear and share N≡1 (mod 4)");

\\ ---------- 3. 4-rank varies inside a public bucket (toy size only) ----------
\\ quadclassunit of |D|~14-bit.  Not a crypto-size computation.
\\ Lists, not Map: this gp's Map/gtos rejects vector keys.
keys = List(); vals = List();
put4(key, r4) = {
  my(i);
  for(i = 1, #keys, \
    if(keys[i]==key, \
      listput(vals, setunion(vals[i], Set([r4])), i); \
      return(0)) \
  );
  listput(keys, key);
  listput(vals, Set([r4]));
};
for(t = 1, 80, \
  pq = far_pair(12, 6); p = pq[1]; q = pq[2]; N = p*q; \
  D0 = fund(N); \
  put4([N%16, rank2(D0)], rank4(D0)) \
);
varied = 0; buckets = #keys;
for(i = 1, buckets, if(#vals[i] > 1, varied++));
printf("  [4-rank] buckets=%d with >1 4-rank: %d (toy |Δ| only)\n", buckets, varied);
check(varied>=1, "4-rank varies inside a public (N mod 16, 2-rank) bucket");

\\ ---------- 4. Shanks is a family: 3 | h(1-4u^3) for u=2..20 ----------
fam = 0;
for(u = 2, 20, \
  D = 1-4*u^3; \
  f = Qfb(u, 1, u^2); \
  if(form_order(f, D)==3 && qfbclassno(D)%3==0, fam++) \
);
check(fam==19, "3 | h(1-4u^3) and Shanks form has order 3 for every u=2..20");

rand3 = 0; rn = 80; got = 0;
while(got < rn, \
  D = coredisc(-(100 + random(20000))); \
  if(D >= -4, next); \
  got++; \
  if(qfbclassno(D)%3==0, rand3++) \
);
printf("  [random fund Δ ~same size] 3|h on %d/%d\n", rand3, rn);
check(rand3 < rn\2, "3|h is common on the Shanks family, not on random fund. Δ");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
