\\ Method 1 — identity sweep.  Hit = a secret DIVIDES public f on
\\ far pairs (f is a public multiple of p±1, p±q, λ, or φ), or
\\ gcd(f,N) in {p,q}, or 4N+f square on far pairs.
\\ Chance gcd>256 of two 16-bit integers is not a handle; 16-bit
\\ maxgcd can be the whole secret by accident.  We count *divides*
\\ frequency.  An identity is frequency = 1.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

setrand(45);

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

Uk(P, n) = {
  if(n==0, return(0));
  if(n==1, return(1));
  a = 0; b = 1;
  for(i = 2, n, t = P*b - a; a = b; b = t);
  b
};

Vk(P, n) = {
  if(n==0, return(2));
  if(n==1, return(P));
  a = 2; b = P;
  for(i = 2, n, t = P*b - a; a = b; b = t);
  b
};

secrets(p, q) = [p-1, p+1, q-1, q+1, p+q, abs(p-q), lcm(p-1,q-1), (p-1)*(q-1)];
sec_names = ["p-1","p+1","q-1","q+1","p+q","|p-q|","λ","φ"];

divides_which(f, secs) = {
  v = [];
  for(i = 1, #secs, if(secs[i]<>0 && f % secs[i]==0, v = concat(v, [i])));
  v
};

poly_names = ["N-1","N+1","2N-1","2N+1","N^2-N+1","N^2+N+1","N^2+1","4N-1","4N+1","4N-4","4N+4"];
poly_at(N, i) = {
  if(i==1, return(N-1));
  if(i==2, return(N+1));
  if(i==3, return(2*N-1));
  if(i==4, return(2*N+1));
  if(i==5, return(N^2-N+1));
  if(i==6, return(N^2+N+1));
  if(i==7, return(N^2+1));
  if(i==8, return(4*N-1));
  if(i==9, return(4*N+1));
  if(i==10, return(4*N-4));
  if(i==11, return(4*N+4));
  0
};

\\ ---------- 0. Polynomial obstruction ----------
cong_fail = 0;
for(t = 1, 40, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  if((N % (p-1)) != (q % (p-1)), cong_fail++); \
  for(i = 1, #poly_names, \
    f = poly_at(N, i); fq = poly_at(q, i); \
    if(gcd(f, p-1) != gcd(fq, p-1), cong_fail++) \
  ) \
);
check(cong_fail == 0, "N≡q (mod p-1) and gcd(f(N),p-1)=gcd(f(q),p-1)");

\\ ---------- 1–2. Polynomials and pairwise gcds on far + 32-bit ----------
score_family(n, gap, nsamp, kind) = {
  npoly = #poly_names;
  divc = matrix(npoly, 8);
  splitc = vector(npoly);
  sqc = vector(npoly);
  for(t = 1, nsamp, \
    pq = far_pair(n, gap); p = pq[1]; q = pq[2]; N = p*q; \
    secs = secrets(p, q); \
    for(i = 1, npoly, \
      f = abs(poly_at(N, i)); \
      w = divides_which(f, secs); \
      for(j = 1, #w, divc[i, w[j]] = divc[i, w[j]]+1); \
      gn = gcd(f, N); if(gn>1 && gn<N, splitc[i]++); \
      d = 4*N + poly_at(N, i); if(d>0 && issquare(d), sqc[i]++) \
    ) \
  );
  any = 0;
  for(i = 1, npoly, \
    row = ""; \
    for(j = 1, 8, \
      if(divc[i,j], row = Strprintf("%s %s:%d/%d", row, sec_names[j], divc[i,j], nsamp)); \
      if(divc[i,j]==nsamp, any++) \
    ); \
    if(splitc[i] || sqc[i] || row!="", \
      printf("  [%s %d-bit] %-10s splitN=%d 4N+fsq=%d%s\n", \
        kind, n, poly_names[i], splitc[i], sqc[i], row) \
    ) \
  );
  any
};

id16 = score_family(16, 10, 80, "poly-far");
id32 = score_family(32, 20, 40, "poly-far");
check(id16==0 && id32==0, "no named poly is a public multiple of a secret on every far pair");

\\ Pairwise gcd(f_i, f_j): identity if a secret always divides that gcd
pair_always = 0; pair_sometimes = 0;
for(i = 1, #poly_names, \
  for(j = i+1, #poly_names, \
    always = 1; some = 0; \
    for(t = 1, 30, \
      pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
      f = gcd(abs(poly_at(N,i)), abs(poly_at(N,j))); \
      w = divides_which(f, secrets(p,q)); \
      if(#w, some=1, always=0) \
    ); \
    if(always && some, pair_always++); \
    if(some && !always, pair_sometimes++) \
  ) \
);
printf("  [gcd pairs] always-divides-a-secret=%d  sometimes=%d\n", pair_always, pair_sometimes);
check(pair_always == 0, "no pairwise gcd is identically a multiple of a secret");

\\ ---------- 3. Φ_k(N) ----------
phi_always = 0;
for(k = 1, 12, \
  always = 1; some = 0; \
  for(t = 1, 30, \
    pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
    f = abs(polcyclo(k, N)); \
    w = divides_which(f, secrets(p,q)); \
    gn = gcd(f, N); \
    if(#w || (gn>1 && gn<N), some=1, always=0) \
  ); \
  if(some, printf("  [Phi_%d] sometimes divides a secret or splits N\n", k)); \
  if(always && some, phi_always++) \
);
check(phi_always == 0, "no Φ_k(N) (k=1..12) is identically a handle");

\\ a^{N±1}-1 materialized only at 8-bit
exp_always = 1; exp_some = 0;
for(t = 1, 20, \
  pq = far_pair(8, 4); p = pq[1]; q = pq[2]; N = p*q; \
  ev = [2^(N+1)-1, 3^(N+1)-1, gcd(2^(N+1)-1, 3^(N+1)-1), 2^N-2]; \
  hit = 0; \
  for(ei = 1, #ev, \
    w = divides_which(ev[ei], secrets(p,q)); \
    gn = gcd(ev[ei], N); \
    if(#w || (gn>1 && gn<N), hit=1) \
  ); \
  if(hit, exp_some=1, exp_always=0) \
);
printf("  [exp 8-bit] always=%d sometimes=%d\n", exp_always && exp_some, exp_some);
check(!(exp_always && exp_some), "2^{N+1}-1 / 3^{N+1}-1 / 2^N-2 not identically handles at 8-bit");

\\ ---------- 4. U_k(N), V_k(N) ----------
uv_always = 0;
for(k = 2, 16, \
  alU = 1; alV = 1; smU = 0; smV = 0; \
  for(t = 1, 25, \
    pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
    secs = secrets(p,q); \
    wU = divides_which(abs(Uk(N,k)), secs); \
    wV = divides_which(abs(Vk(N,k)), secs); \
    if(#wU, smU=1, alU=0); \
    if(#wV, smV=1, alV=0) \
  ); \
  if(smU, printf("  [U_%d(N)] sometimes a secret divides it\n", k)); \
  if(smV, printf("  [V_%d(N)] sometimes a secret divides it\n", k)); \
  if(alU && smU, uv_always++); \
  if(alV && smV, uv_always++) \
);
check(uv_always == 0, "no U_k(N)/V_k(N) (k=2..16) is identically a handle");

\\ Cheap Δ probe — not a new bit
jac_m = 0; jac_n = 80;
for(t = 1, jac_n, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; s = p+q; \
  if((kronecker(-4*N, 5)==1) == (s%4==0), jac_m++) \
);
printf("  [kronecker(-4N/5) vs s≡0 (mod 4)] %.3f\n", jac_m/jac_n);
check(1, "kronecker probe recorded");

\\ ---------- 5. Type A contrast ----------
close_sq = 0; close_n = 25;
for(t = 1, close_n, \
  p = nbit_prime(16); q = nextprime(p+1); \
  if(issquare((p+q)^2 - 4*p*q), close_sq++) \
);
check(close_sq == close_n, "(p+q)^2-4N is always square (Fermat, Type A)");

close_poly_near = 0;
for(t = 1, 20, \
  p = nbit_prime(16); q = nextprime(p+1); N = p*q; s2 = 2*sqrtint(N); \
  for(i = 1, #poly_names, if(abs(poly_at(N,i)-s2) < 2^6, close_poly_near++)) \
);
check(close_poly_near == 0, "named polys stay size N, not 2√N, on close primes");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
