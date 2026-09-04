\\ If the top Fermat-fold class r = q−2 is 0 mod q, the leftover
\\ at the F_q* boundary is killed: fold_q = X^{d_q} as a polynomial
\\ mod q.  Binomial and binomial + N X^20 have top class 0.
\\ The geometric kernel (X^{q−1}−1)/(X−p) has top class 1 and
\\ does not invert F_p*.  Mirrors SrsaRootPoly.v.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; e=pin_e;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;

Pbin=ca*x^da + cb*x^db;
top=0; for(j=0, 5, top += polcoeff(Pbin, (q-2)+j*(q-1)));
check(top%q==0,                         "binomial top class q−2 is 0 mod q");
exact=1;
for(r=0, q-2, \
  cs=0; for(j=0, 5, cs += polcoeff(Pbin, r+j*(q-1))); \
  want=if(r==db, 1, 0); \
  if(cs%q != want, exact=0) \
);
check(exact,                            "top class 0 ⇒ binomial fold_q is X^{d_q}");

Pinv=ca*x^da + cb*x^db + N*x^20;
top20=0; for(j=0, 8, top20 += polcoeff(Pinv, (q-2)+j*(q-1)));
check(top20%q==0,                       "binomial + N X^{20} top class still 0 mod q");
exact20=1;
for(r=0, q-2, \
  cs=0; for(j=0, 8, cs += polcoeff(Pinv, r+j*(q-1))); \
  want=if(r==db, 1, 0); \
  if(cs%q != want, exact20=0) \
);
check(exact20,                          "top class 0 ⇒ invert poly fold_q is X^{d_q}");

K=0; for(j=0, q-2, K += p^j * x^(q-2-j));
check(poldegree(K)==q-2,                "geometric kernel deg q−2");
check(polcoeff(K,q-2)%q!=0,             "kernel top class nonzero mod q");
van=1;
for(aa=1, q-1, \
  if(aa!=p, if(lift(Mod(subst(K,x,aa),q))!=0, van=0)) \
);
check(van,                              "kernel vanishes on F_q* minus p");
miss2=lift((Mod(ca*2^da + cb*2^db + subst(K,x,2), N)^e));
check(miss2!=2,                         "binomial + kernel does not invert unit 2");

q2=pin1363_q; db2=pin1363_inv3_q;
P2=pin1363_root_ca*x^pin1363_inv3_p + pin1363_root_cb*x^pin1363_inv3_q;
ex2=1;
for(r=0, q2-2, \
  cs=polcoeff(P2, r); \
  want=if(r==db2, 1, 0); \
  if(cs%q2 != want, ex2=0) \
);
check(ex2,                              "1363 binomial fold_q is X^{d_q}");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
