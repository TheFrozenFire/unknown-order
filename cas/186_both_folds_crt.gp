\\ Both Fermat folds of an invert poly are the local inverse
\\ monomials.  The unique nonzero class mod p is d_p, unique
\\ nonzero class mod q is d_q, and CRT of those is d mod λ.
\\ Mirrors SrsaRootPoly.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; d=pin_d; lam=pin_lam;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;
Pinv=ca*x^da + cb*x^db + N*x^20;

fp=1;
for(r=0, p-2, \
  cs=0; for(j=0, 6, cs += polcoeff(Pinv, r+j*(p-1))); \
  want=if(r==da, 1, 0); \
  if(cs%p != want, fp=0) \
);
check(fp,                               "fold_p is X^{d_p}");
fq=1;
for(r=0, q-2, \
  cs=0; for(j=0, 8, cs += polcoeff(Pinv, r+j*(q-1))); \
  want=if(r==db, 1, 0); \
  if(cs%q != want, fq=0) \
);
check(fq,                               "fold_q is X^{d_q}");
crt=lift(chinese(Mod(da,p-1), Mod(db,q-1)));
check(crt==d%lam,                       "CRT(d_p, d_q) = d mod λ");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
