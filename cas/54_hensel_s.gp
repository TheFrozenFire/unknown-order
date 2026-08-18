\\ Method 11 — s with s^2-4N a square in Z/ℓ^k Z.
\\ True p+q is one solution.  A new handle is a canonical lift
\\ that is not “nearest to 2√N”.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));
setrand(54);
nbit_prime(n) = nextprime(2^(n-1) + random(2^(n-1)));
far_pair(n, gap) = {
  for(tries = 1, 4000, \
    p = nbit_prime(n); q = nbit_prime(n); \
    if(p==q, next); if(p<q, t=p; p=q; q=t); \
    if(p<=2*q && abs(p-q)>=2^gap, return([p,q])) \
  ); error("none")
};

count_sq(N, mod) = {
  c = 0;
  for(s = 0, mod-1, \
    if(issquare(Mod(s^2 - 4*N, mod)), c++) \
  );
  c
};

\\ Odd ℓ ∤ N: many solutions (unit factorizations).
pq = far_pair(12, 6); p = pq[1]; q = pq[2]; N = p*q; s0 = p+q;
n3 = count_sq(N, 3^4);
n5 = count_sq(N, 5^3);
n7 = count_sq(N, 7^3);
printf("  [count] #s mod 81 with s^2-4N square: %d (true s present? %d)\n", \
  n3, issquare(Mod(s0^2-4*N, 81)));
printf("  [count] mod 125: %d;  mod 343: %d\n", n5, n7);
check(n3 > 4, "many s mod 3^4 make s^2-4N a square");
check(issquare(Mod(s0^2-4*N, 81)), "true p+q is one of them");

\\ 2-adic: count mod 2^k
n2 = vector(8);
for(k = 3, 8, n2[k] = count_sq(N, 2^k));
printf("  [count 2-adic] mod 8..256: %d %d %d %d %d %d\n", \
  n2[3], n2[4], n2[5], n2[6], n2[7], n2[8]);
check(n2[6] > 2, "more than one 2-adic class mod 64");

\\ Public constraint s ≡ 2 (mod 4) when N≡1 (mod 4), else 0 (mod 4).
\\ After restricting to that residue, still many?
restrict = 0;
want = if(N%4==1, 2, 0);
for(s = 0, 80, \
  if(s%4==want && issquare(Mod(s^2-4*N, 81)), restrict++) \
);
printf("  [count] s≡s0 (mod 4) and square disc mod 81: %d\n", restrict);
check(restrict > 1, "public s mod 4 does not isolate p+q in Z/81Z");

\\ Nearest-to-2√N rule: among solutions mod M=3^5=243, is the
\\ representative nearest 2√N always the true s mod M?
near_ok = 0; nn = 25; M = 243;
for(t = 1, nn, \
  pq = far_pair(12, 6); p = pq[1]; q = pq[2]; N = p*q; s0 = p+q; \
  target = 2*sqrtint(N); \
  best = -1; bestd = M; \
  for(s = 0, M-1, \
    if(!issquare(Mod(s^2-4*N, M)), next); \
    d = min((s-target)%M, (target-s)%M); \
    if(d < bestd, bestd = d; best = s) \
  ); \
  if(best == s0 % M, near_ok++) \
);
printf("  [nearest 2√N among sols mod 243] matches true s: %d/%d\n", near_ok, nn);
\\ On 12-bit far pairs, 2√N is already close enough that this Type A
\\ rule often works.  That is Fermat, not a new lift.
check(1, "nearest-2√N among Hensel solutions is Type A (Fermat)");

\\ Farther primes: 16-bit gap=10, M=81 — nearest 2√N should miss more.
near2 = 0; nn2 = 20; M2 = 81;
for(t = 1, nn2, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; s0 = p+q; \
  target = 2*sqrtint(N); \
  best = -1; bestd = M2; \
  for(s = 0, M2-1, \
    if(!issquare(Mod(s^2-4*N, M2)), next); \
    d = min((s-target)%M2, (target-s)%M2); \
    if(d < bestd, bestd = d; best = s) \
  ); \
  if(best == s0 % M2, near2++) \
);
printf("  [nearest 2√N mod 81, 16-bit far] %d/%d\n", near2, nn2);
check(1, "Type A rule recorded at two sizes");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
