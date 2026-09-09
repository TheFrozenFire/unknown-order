\\ Sequential miller-base search: a = 2, 3, ... until miller_walk
\\ returns a proper factor.  On this pin the first hit is 2.
\\ miller_walk of 1 and -1 is empty (liars).  Mirrors
\\ miller_search / pin_miller_search.  Not residual-solver =>
\\ factor for every RSAInstance.  Probe names avoid the word "fail".

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

miller_search(N, M) = {
  hit = [0, 0];
  for(a = 2, N-2, \
    f = miller_walk(N, M, a); \
    if(f>1 && f<N && N%f==0, hit=[a, f]; break) \
  );
  hit
};

N=pin_N; M=pin_lam; p=pin_p;
hit=miller_search(N, M);
check(hit[1]==2,                        "first hit is base 2");
check(hit[2]==p,                        "that walk returns p");
check(miller_walk(N, M, 1)==0,          "base 1 is a miller liar");
check(miller_walk(N, M, N-1)==0,        "base -1 is a miller liar");

\\ a unit other than plus/minus 1 whose walk is empty
liar=0;
for(a = 3, N-3, \
  if(gcd(a,N)==1 && miller_walk(N, M, a)==0, liar=a; break) \
);
check(liar>1 && liar<N-1,               "some interior unit is a miller liar");
printf("  [liar] a = %d\n", liar);

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
