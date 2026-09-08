\\ Invert-all-units polynomial at residual e=7 is y |-> y^23.
\\ X^23 inverts every unit at e=7; Miller from 7*23-1=160.
\\ Mirrors invert_all_units_poly_at_e / pin_X23_inverts_at_7.
\\ Not residual-solver => factor: a solver is not a polynomial.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

oddpart(n) = { while(n%2==0, n = n/2); n };

N=pin_N; p=pin_p; e=7; d=23;
M=x^d;
okx=1;
for(yy=1, N-1, \
  if(gcd(yy,N)==1, \
    yd=lift(Mod(yy,N)^d); \
    if(lift(Mod(subst(M,x,yy),N))!=yd, okx=0); \
    if(lift(Mod(yd,N)^e)!=yy, okx=0) \
  ) \
);
check(okx,                              "X^23 is y^23 and a 7th root on every unit");
check((e*d)%pin_lam==1,                 "7*23 cong 1 mod lam");
check(gcd(lift(Mod(2,N)^(oddpart(e*d-1)*2))-1, N)==p, "Miller on 160 splits");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
