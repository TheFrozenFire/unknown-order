\\ Lift extract-then-Miller headlines off pin 187.
\\ N=13*19=247, λ=36, e=5, d'=29, 5*29≡1 (mod 36).
\\ Mirrors residual_inv_mod_lambda,
\\ residual_leaf_order_lambda_extracts_and_factors,
\\ miller_search_hits_semiprime,
\\ invert_all_units_poly_at_e_semiprime.
\\ Pin 187 stays cas/238–248.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

oddpart(n) = { while(n%2==0, n = n/2); n };
val2(n) = valuation(n, 2);

miller_walk(N, M, a) = {
  if(M<=0, return(0));
  t = oddpart(M); s = val2(M);
  g = lift(Mod(a,N)^t);
  for(i = 1, s, \
    ng = lift(Mod(g,N)^2); \
    if(ng==1, \
      if(g==1 || g==N-1, return(0), return(gcd(g-1, N))) \
    ); \
    g = ng \
  );
  0
};

miller_search(N, M) = {
  for(a = 2, N-2, \
    f = miller_walk(N, M, a); \
    if(f>1 && f<N, return([a, f])) \
  );
  [0, 0]
};

p=13; q=19; N=p*q; e=5; lam=lcm(p-1,q-1);
b=gcdext(e,lam); dp=lift(Mod(e,lam)^(-1));
M=e*dp-1;
g=lift(chinese(Mod(znprimroot(p),p), Mod(znprimroot(q),q)));
sm=lift(chinese(Mod(1,p), Mod(-1,q)));

check(N==247,                           "N=13*19=247");
check(lam==36,                          "lambda=36");
check(gcd(e,lam)==1,                    "gcd(5,36)=1");
check(b[1]*e + b[2]*lam==1,             "Bezout 5*u + 36*v = 1");
check((dp%lam)==29,                     "5 inverse is 29");
check((e*29)%lam==1,                    "5*29 cong 1 mod lam");
check(M==144 && M%lam==0,               "e d'-1 is a lam-multiple");
check(M%2==0,                           "M is even");
check(znorder(Mod(g,N))==lam,           "g has order lambda");
check(sm>1 && sm<N-1,                   "mixed sqrt1 in 2..N-2");
check(lift(Mod(sm,N)^2)==1,             "mixed sqrt1 squares to 1");
check(gcd(sm-1,N)==p || gcd(sm-1,N)==q, "mixed sqrt1 gcd splits");
check(miller_walk(N, M, sm%N)==p || miller_walk(N, M, sm%N)==q, "walk of mixed sqrt1 splits");
hit=miller_search(N, lam);
check(hit[1]>=2 && hit[1]<=N-2,         "search hit in 2..N-2");
check(hit[2]==p || hit[2]==q,           "search at lam splits");
hitM=miller_search(N, M);
check(hitM[2]==p || hitM[2]==q,         "search at e d'-1 splits");

\\ Trapdoor monomial X^29 inverts every unit at e=5.
units_ok=1;
for(yy=1, N-1, \
  if(gcd(yy,N)==1, \
    if(lift(Mod(yy,N)^(dp*e))!=yy, units_ok=0) \
  ) \
);
check(units_ok,                         "X^{d'} inverts every unit at e=5");

\\ dlog of trapdoor at g recovers d'.
xg=lift(Mod(g,N)^dp);
check(xg==lift(Mod(g,N)^29),            "g^{d'} is the trapdoor image");

\\ Residual leaf at g: x = g^{d'}, x^e = g.
check(lift(Mod(xg,N)^e)==g%N || lift(Mod(xg,N)^e)==lift(Mod(g,N)), "leaf x^e = g");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
