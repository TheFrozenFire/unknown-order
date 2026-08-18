\\ Method 5 — recurrences whose char poly involves N.
\\ U_k(N), V_k(N) with P=N (x^2 - N x + 1).  Also x^2 - x + N and x^2 + N.
\\ gcd(U_k(N), N) and rank of appearance of p vs p±1.
\\ (N^2-4 / p) = (q^2-4 / p) is NOT (N^2-4 / N) = (-4/N).

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));
setrand(48);
nbit_prime(n) = nextprime(2^(n-1) + random(2^(n-1)));
far_pair(n, gap) = {
  for(tries = 1, 4000, \
    p = nbit_prime(n); q = nbit_prime(n); \
    if(p==q, next); if(p<q, t=p; p=q; q=t); \
    if(p<=2*q && abs(p-q)>=2^gap, return([p,q])) \
  ); error("none")
};

Uk(P, n) = {
  if(n==0, return(0)); if(n==1, return(1));
  a = 0; b = 1;
  for(i = 2, n, t = P*b - a; a = b; b = t);
  b
};

\\ Rank of appearance of p in U_*(N): smallest k>0 with p | U_k(N).
zapp(P, pr, kmax) = {
  a = 0; b = 1;
  if(b % pr==0, return(1));
  for(k = 2, kmax, \
    t = (P*b - a) % pr; a = b; b = t; \
    if(b==0, return(k)) \
  );
  0
};

\\ gcd(U_k(N), N) never splits far N for k=2..40
split = 0;
for(t = 1, 30, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  for(k = 2, 40, \
    g = gcd(abs(Uk(N,k)), N); \
    if(g>1 && g<N, split++) \
  ) \
);
printf("  [gcd(U_k(N),N) k=2..40] splits=%d\n", split);
check(split==0, "U_k(N) does not split far N for k≤40");

\\ Rank of p in U_*(N) vs p±1.  Period of x^2-Nx+1 mod p
\\ divides p-(Δ/p) where Δ=N^2-4 ≡ q^2-4 (mod p).
div_pm1 = 0; nzk = 0; ns = 40; kmax = 80;
for(t = 1, ns, \
  pq = far_pair(12, 6); p = pq[1]; q = pq[2]; N = p*q; \
  z = zapp(N % p, p, kmax); \
  if(z==0, next); \
  nzk++; \
  if((p-1)%z==0 || (p+1)%z==0, div_pm1++) \
);
printf("  [Z(p) in U_*(N)] found=%d/%d  divides p±1: %d\n", nzk, ns, div_pm1);
check(nzk==0 || div_pm1==nzk, "when the rank of appearance exists below 80 it divides p±1 (Williams)");

\\ Jacobi chase: (N^2-4 / p) vs (N^2-4 / N)
jac_pub = 0; jac_sec = 0; jn = 60;
for(t = 1, jn, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  pub = kronecker(N^2-4, N); \
  sec = kronecker(N^2-4, p); \
  if(pub == sec, jac_pub++) \
);
printf("  [(N^2-4/p) == (N^2-4/N)] %d/%d  (public is (-4/N), not the period discriminant)\n", jac_pub, jn);
check(jac_pub < jn*8\10, "(N^2-4/p) is not the public (N^2-4/N)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
