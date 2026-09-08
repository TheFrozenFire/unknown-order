\\ CRT binomial and trapdoor monomial X^d both invert every unit.
\\ Their difference has both Fermat folds zero: they are the same
\\ local inverse maps, different polynomials.  Writing either
\\ writes d_p and d_q.  Mirrors SrsaRootPoly.v.  Probe names
\\ avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; d=pin_d;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;
P=ca*x^da + cb*x^db;
M=x^d;
D=P-M;
fp=1;
for(r=0, p-2, \
  cs=0; for(j=0, 6, cs += polcoeff(D, r+j*(p-1))); \
  if(cs%p!=0, fp=0) \
);
check(fp,                               "binomial − X^d fold_p = 0");
fq=1;
for(r=0, q-2, \
  cs=0; for(j=0, 8, cs += polcoeff(D, r+j*(q-1))); \
  if(cs%q!=0, fq=0) \
);
check(fq,                               "binomial − X^d fold_q = 0");
crt=lift(chinese(Mod(da,p-1), Mod(db,q-1)));
check(crt==d%pin_lam,                   "CRT(d_p, d_q) = d mod λ");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
