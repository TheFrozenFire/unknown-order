\\ The CRT binomial inhabitant has both Fermat folds equal to
\\ the local inverse monomials, and CRT of those degrees is d
\\ mod λ.  Writing the binomial wrote {p,q} into the coeffs and
\\ d into the folds.  Mirrors SrsaRootPoly.v.  Probe names avoid
\\ the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; d=pin_d; lam=pin_lam;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;
P=ca*x^da + cb*x^db;

fp=1;
for(r=0, p-2, \
  cs=polcoeff(P, r); \
  want=if(r==da, 1, 0); \
  if(cs%p != want, fp=0) \
);
check(fp,                               "CRT binomial fold_p is X^{d_p}");
fq=1;
for(r=0, q-2, \
  cs=polcoeff(P, r); \
  want=if(r==db, 1, 0); \
  if(cs%q != want, fq=0) \
);
check(fq,                               "CRT binomial fold_q is X^{d_q}");
crt=lift(chinese(Mod(da,p-1), Mod(db,q-1)));
check(crt==d%lam,                       "CRT(d_p, d_q) = d mod λ");
check(gcd(ca,N)==q,                     "c_p splits (writes q)");
check(gcd(cb,N)==p,                     "c_q splits (writes p)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
