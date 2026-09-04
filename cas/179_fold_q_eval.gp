\\ Fermat fold on F_q*: an all-units invert poly matches X^{d_q}
\\ on F_q* samples after folding classes mod (q−1).  Only q−2
\\ samples (residue p is missing), so this is functional agreement,
\\ not yet a polynomial identity.  Mirrors SrsaRootPoly.v.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; e=pin_e;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;

Pinv=ca*x^da + cb*x^db + N*x^20;
funok=1;
for(aa=1, q-1, \
  if(gcd(aa,N)==1, \
    fv=0; \
    for(r=0, q-2, \
      cs=0; for(j=0, 8, cs += polcoeff(Pinv, r+j*(q-1))); \
      fv += cs*aa^r \
    ); \
    if(fv%q != lift(Mod(aa,q)^db), funok=0) \
  ) \
);
check(funok,                            "fold_q of invert poly agrees with X^{d_q} on F_q* samples");
check(lift(Mod(2,q)^(q-1))==1,          "Fermat: 2^{q−1}≡1 on F_q*");
check(p < q,                            "missing F_q* sample is residue p");

P2=pin1363_root_ca*x^pin1363_inv3_p + pin1363_root_cb*x^pin1363_inv3_q;
q2=pin1363_q; db2=pin1363_inv3_q; N2=pin1363_N;
fun2=1;
for(aa=1, q2-1, \
  if(gcd(aa,N2)==1, \
    fv=0; \
    for(r=0, q2-2, \
      fv += polcoeff(P2, r)*aa^r \
    ); \
    if(fv%q2 != lift(Mod(aa,q2)^db2), fun2=0) \
  ) \
);
check(fun2,                             "1363 binomial fold_q agrees on F_q* samples");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
