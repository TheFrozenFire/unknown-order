\\ Invert-all-units implies fold_q is X^{d_q} as a polynomial
\\ (class d_q is 1, every other class 0, including the top class
\\ q−2).  No leftover, no extra top-zero hypothesis.
\\ Mirrors SrsaRootPoly.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

q=pin_q; N=pin_N;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;
Pinv=ca*x^da + cb*x^db + N*x^20;

exact=1;
for(r=0, q-2, \
  cs=0; for(j=0, 8, cs += polcoeff(Pinv, r+j*(q-1))); \
  want=if(r==db, 1, 0); \
  if(cs%q != want, exact=0) \
);
check(exact,                            "invert poly fold_q is X^{d_q} as a polynomial");
top=0; for(j=0, 8, top += polcoeff(Pinv, (q-2)+j*(q-1)));
check(top%q==0,                         "top class q−2 is 0 (leftover killed)");

P2=pin1363_root_ca*x^pin1363_inv3_p + pin1363_root_cb*x^pin1363_inv3_q;
q2=pin1363_q; db2=pin1363_inv3_q;
ex2=1;
for(r=0, q2-2, \
  cs=polcoeff(P2, r); \
  want=if(r==db2, 1, 0); \
  if(cs%q2 != want, ex2=0) \
);
check(ex2,                              "1363 binomial fold_q is X^{d_q}");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
