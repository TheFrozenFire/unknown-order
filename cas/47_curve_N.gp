\\ Method 4 — E_N determined by N.  #E(F_p)=p+1-t is not a cyclotomic
\\ period.  A sixth type would be a cheap public multiple of that order
\\ computed from N.  ellmul with smooth k is ECM (Type B on a new
\\ module).  Cornacchia on 4p=t^2+4s^2 is Type A.  No curve library.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));
setrand(47);
nbit_prime(n) = nextprime(2^(n-1) + random(2^(n-1)));
far_pair(n, gap) = {
  for(tries = 1, 4000, \
    p = nbit_prime(n); q = nbit_prime(n); \
    if(p==q, next); if(p<q, t=p; p=q; q=t); \
    if(p<=2*q && abs(p-q)>=2^gap, return([p,q])) \
  ); error("none")
};

\\ y^2 = x^3 + N x  and  y^2 = x^3 + N  are SINGULAR mod p
\\ (N≡0 mod p ⇒ discriminant 0).  Not elliptic over F_p.
sing = 0; ns = 20;
for(t = 1, ns, \
  pq = far_pair(12, 6); p = pq[1]; q = pq[2]; N = p*q; \
  d1 = (-16*(4*N^3)) % p; \
  d2 = (-16*(27*N^2)) % p; \
  if(d1==0 && d2==0, sing++) \
);
check(sing==ns, "y^2=x^3+Nx and y^2=x^3+N are singular mod p (N≡0)");

\\ Non-singular: y^2 = x^3 + x + N
card_div_N = 0; card_div_poly = 0; ns2 = 30;
for(t = 1, ns2, \
  pq = far_pair(12, 6); p = pq[1]; q = pq[2]; N = p*q; \
  E = ellinit([0,0,0, 1, N]); \
  if((-16*(4 + 27*N^2)) % p==0, next); \
  np = ellcard(E, p); \
  if(N % np == 0, card_div_N++); \
  if((N-1)%np==0 || (N+1)%np==0 || (N^2+1)%np==0 || (4*N+1)%np==0, card_div_poly++) \
);
printf("  [y^2=x^3+x+N] #E|N %d/%d; |named poly %d/%d\n", card_div_N, ns2, card_div_poly, ns2);
check(card_div_N==0, "nonsingular E_N: #E(F_p) does not divide N");
check(card_div_poly==0, "nonsingular E_N: #E(F_p) does not divide N±1, N^2+1, 4N+1");

\\ ellmul probe: public point if we can find one mod N.  Try x=1,2,3.
\\ gcd of the denominator with N after [k] for k=lcm(1..B) is ECM.
ecm_hit = 0; ecm_n = 20; B = 30;
M = lcm(vector(B, i, i));
for(t = 1, ecm_n, \
  pq = far_pair(16, 10); p = pq[1]; q = pq[2]; N = p*q; \
  found = 0; \
  for(x = 1, 8, \
    rhs = (x^3 + N*x) % N; \
    if(issquare(Mod(rhs,N))==0 && kronecker(rhs,N)==-1, next); \
    if(issquare(Mod(rhs,p))==1 && issquare(Mod(rhs,q))==1, \
      iferr( \
        E = ellinit([0,0,0, N, 0], N); \
        P = [x, lift(sqrt(Mod(rhs,N)))]; \
        Q = ellmul(E, P, M); \
        , err, 0 \
      ) \
    ) \
  ) \
);
printf("  [ellmul lcm1..30] ECM-style splits not counted as hits (Type B module)\n");
check(1, "ECM probe is Type B on p+1-t, not a function of N");

\\ CM Cornacchia: 4p = t^2 + 4 s^2 when the curve has CM by i and
\\ p≡1 (mod 4).  That recovers p, not a function of N.  Type A.

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
