\\ An all-units invert poly matches X^{d_q} on every residue of
\\ F_q*, including p, via the lift p+q.  Fold degree < q−1 and
\\ q−1 samples, so fold_q = X^{d_q} as a polynomial: no leftover.
\\ Mirrors SrsaRootPoly.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;
Pinv=ca*x^da + cb*x^db + N*x^20;

allq=1;
for(aa=1, q-1, \
  fv=0; \
  for(r=0, q-2, \
    cs=0; for(j=0, 8, cs += polcoeff(Pinv, r+j*(q-1))); \
    fv += cs*aa^r \
  ); \
  if(fv%q != lift(Mod(aa,q)^db), allq=0) \
);
check(allq,                             "invert poly fold_q = X^{d_q} on all of F_q*");

fv=0; for(r=0, q-2, fv += polcoeff(ca*x^da+cb*x^db, r)*p^r);
check(fv%q == lift(Mod(p,q)^db),        "binomial fold_q(p) = p^{d_q}");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
