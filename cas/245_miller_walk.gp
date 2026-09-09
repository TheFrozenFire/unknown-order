\\ Miller square-chain from (N, M, a): walk g0 = a^t, square,
\\ return gcd(g-1, N) at the first mixed sqrt1.  No height kp
\\ from p in the construction.  Mirrors miller_walk /
\\ pin_miller_walk_base2.  Not residual-solver => factor for
\\ every RSAInstance.  Probe names avoid the word "fail".

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

N=pin_N; M=pin_lam; p=pin_p;
t=oddpart(M); s=val2(M);

check(t==5,                             "t = odd_part(80) = 5");
check(s==4,                             "s = val2(80) = 4");
g0=lift(Mod(2,N)^t);
check(g0==32,                           "g0 = 2^5 = 32");
check(gcd(g0-1, N)==1,                  "split is not at g0");
g1=lift(Mod(g0,N)^2);
check(g1==89,                           "32^2 cong 89");
g2=lift(Mod(g1,N)^2);
check(g2==67,                           "89^2 cong 67");
g3=lift(Mod(g2,N)^2);
check(g3==1,                            "67^2 cong 1");
check(g2!=1 && g2!=N-1,                 "67 is not plus/minus 1");
check(gcd(g2-1, N)==p,                  "gcd(66,187) = 11");
check(miller_walk(N, M, 2)==p,          "miller_walk(N, lam, 2) = p");
check(miller_walk(N, M, 1)==0,          "base 1 is a miller liar");
check(miller_walk(N, M, N-1)==0,        "base -1 is a miller liar");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
