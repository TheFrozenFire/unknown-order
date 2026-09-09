\\ Residual leaf miller step is miller_walk(N, e*d'-1, 2), not
\\ gcd(2^{t * 2^kp}-1, N) with kp from p.  Cube: e=3 d'=27 M=80.
\\ 7th: e=7 d'=23 M=160.  Mirrors pin_miller_walk_from_lambda_multiple
\\ / residual_leaf_at_g_extracts_and_factors.  Not residual-solver
\\ => factor for every RSAInstance.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

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

N=pin_N; p=pin_p;
M3=pin_e*pin_d-1;
M7=7*23-1;
check(M3==pin_lam,                      "3*27-1 = lam");
check(M7==160,                          "7*23-1 = 160");
check(M3%pin_lam==0 && M7%pin_lam==0,   "both M are lam-multiples");
check(miller_walk(N, M3, 2)==p,         "walk at M=lam base 2 splits");
check(miller_walk(N, M7, 2)==p,         "walk at M=160 base 2 splits");
check(miller_walk(N, M3, 2)!=0,         "walk is the gcd, not empty");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
