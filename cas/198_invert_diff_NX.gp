\\ Two invert-all-units polys (CRT binomial and binomial + N X^20)
\\ have difference with both Fermat folds zero.  The junk is an
\\ N-multiple, invisible in both Fermat rings.  Mirrors
\\ SrsaRootPoly.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;
P1=ca*x^da + cb*x^db;
P2=P1 + N*x^20;
D=P1-P2;
fp=1;
for(r=0, p-2, \
  cs=0; for(j=0, 6, cs += polcoeff(D, r+j*(p-1))); \
  if(cs%p!=0, fp=0) \
);
check(fp,                               "diff fold_p = 0");
fq=1;
for(r=0, q-2, \
  cs=0; for(j=0, 8, cs += polcoeff(D, r+j*(q-1))); \
  if(cs%q!=0, fq=0) \
);
check(fq,                               "diff fold_q = 0");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
