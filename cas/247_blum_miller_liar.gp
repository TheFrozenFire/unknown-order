\\ Blum extra 11×19=209, λ=90: miller_walk at base 2 does not
\\ split (matching v2(ord 2)); base 3 does.  Campaign pin stays
\\ 187.  pin_77 is the wrong extra (base 2 still hits there).
\\ Mirrors pin_209_miller_walk_base2_liar / pin_209_miller_walk_base3.
\\ Not residual-solver => factor for every RSAInstance.
\\ Probe names avoid the word "fail".

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

N=pin_209; lam=pin_209_lam; p=pin_209_p; q=pin_209_q;

check(N==11*19,                         "N = 11*19 = 209");
check(lam==lcm(10,18),                  "lam = lcm(10,18) = 90");
check(val2(p-1)==1 && val2(q-1)==1,     "Blum (1,1)");
check(val2(znorder(Mod(2,p)))==1,       "v2(ord_p 2) = 1");
check(val2(znorder(Mod(2,q)))==1,       "v2(ord_q 2) = 1");
check(lift(Mod(2,N)^oddpart(lam))==N-1, "g0 of base 2 is -1");
check(miller_walk(N, lam, 2)==0,        "base 2 is a miller liar");
check(miller_walk(N, lam, 3)==p,        "base 3 splits");
check(pin_N==187,                       "campaign alias stays 187");
check(miller_walk(pin_77, pin_77_lam, 2)>1, "pin_77 base 2 still hits");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
