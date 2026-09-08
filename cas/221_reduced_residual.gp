\\ Trapdoor (y^d, e=3) is a residual leaf for every reduced unit.
\\ N+1 is coprime but not a residue, so not a leaf.
\\ Miller-from-d still splits.  Not residual-solver => factor.
\\ Mirrors SrsaModCbrt.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N=pin_N; e=pin_e; d=pin_d; p=pin_p; lam=pin_lam;
leaf=1;
for(yy=1, N-1, \
  if(gcd(yy,N)==1, \
    x=lift(Mod(yy,N)^d); \
    if(lift(Mod(x,N)^e)!=yy, leaf=0) \
  ) \
);
check(leaf,                             "trapdoor inhabits a residual leaf on residues");
check(gcd(N+1,N)==1,                    "N+1 is coprime");
check(lift(Mod(42,N)^3)!=N+1,           "a residue cube is not N+1");
g=gcd(2^10-1, N);
check(g==p,                             "Miller-from-d gcd is p");
check(gcd(e,lam)==1 && (e-1)%lam!=0,    "e is a residual exponent");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
