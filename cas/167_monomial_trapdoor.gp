\\ A monomial X^k inverts every unit iff e·k ≡ 1 (mod λ):
\\ k is a decryption exponent.  Local inverses d_p, d_q invert
\\ one prime field, not (Z/NZ)*.  k = d + λ also works.
\\ Mirrors SrsaRootPoly.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; e=pin_e; d=pin_d; lam=pin_lam;
g=pin_g; da=pin_inv3_p; db=pin_inv3_q;

check(znorder(Mod(g,N))==lam,           "ord(g)=λ");
check((e*d)%lam==1,                     "e·d ≡ 1 (mod λ)");
check(lift((Mod(g,N)^d)^e)==g,          "g^d is the e-th root of g");

check((e*da)%lam!=1,                    "e·d_p ≢ 1 (mod λ)");
check((e*db)%lam!=1,                    "e·d_q ≢ 1 (mod λ)");
check(lift((Mod(g,N)^da)^e)!=g,         "X^{d_p} does not invert g");
check(lift((Mod(g,N)^db)^e)!=g,         "X^{d_q} does not invert g");
check(lift((Mod(2,N)^da)^e)!=2,         "X^{d_p} does not invert unit 2");
check(lift((Mod(2,N)^db)^e)!=2,         "X^{d_q} does not invert unit 2");

k2=d+lam;
check((e*k2)%lam==1,                    "e·(d+λ) ≡ 1 (mod λ)");
check(lift((Mod(g,N)^k2)^e)==g,         "X^{d+λ} inverts g");

units_d=1; units_k2=1; units_da=1;
for(aa=1, N-1, \
  if(gcd(aa,N)==1, \
    if(lift((Mod(aa,N)^d)^e)!=aa, units_d=0); \
    if(lift((Mod(aa,N)^k2)^e)!=aa, units_k2=0); \
    if(lift((Mod(aa,N)^da)^e)!=aa, units_da=0) \
  ) \
);
check(units_d,                          "X^d inverts every unit");
check(units_k2,                         "X^{d+λ} inverts every unit");
check(units_da==0,                      "X^{d_p} misses some unit");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
