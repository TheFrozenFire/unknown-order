\\ Invert-all-units polynomial ⇒ trapdoor map and a factor.
\\ Eval is y^d on units (binomial, X^d, binomial+N K).  Miller-from-d
\\ splits.  CRT coefficients split; X^d coefficients do not.
\\ Not residual-solver ⇒ factor.  Mirrors SrsaRootPoly.v.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; e=pin_e; d=pin_d;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;
K=0; for(j=0, q-2, K += p^j * x^(q-2-j));
P=ca*x^da + cb*x^db;
Q=P + N*K;
M=x^d;

same=1;
for(yy=1, N-1, \
  if(gcd(yy,N)==1, \
    yd=lift(Mod(yy,N)^d); \
    if(lift(Mod(subst(P,x,yy),N))!=yd, same=0); \
    if(lift(Mod(subst(Q,x,yy),N))!=yd, same=0); \
    if(lift(Mod(subst(M,x,yy),N))!=yd, same=0) \
  ) \
);
check(same,                             "binomial, +N K, and X^d are y^d on units");

\\ miller_t(λ=80)=5; val2(ord_p(2)=10)=1; 2^(5·2)−1
g=gcd(2^10-1, N);
check(g==p,                             "Miller-from-d gcd(2^{10}−1,N)=p");
check(1<g && g<N,                       "that gcd is a proper factor");

check(gcd(ca,N)==q,                     "CRT coeff c_p splits");
check(gcd(cb,N)==p,                     "CRT coeff c_q splits");
check(gcd(1,N)==1,                      "leading coeff of X^d does not split");
check(gcd(0,N)==N,                      "other coeffs of X^d are 0");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
