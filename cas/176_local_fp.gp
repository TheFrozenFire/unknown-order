\\ An all-units e-th-root poly matches X^{d_p} on every residue of
\\ F_p*, with no degree bound.  Campaign pins have p < q, so every
\\ residue of F_p* is a unit of Z/NZ (q is not among 1..p−1).  The
\\ F_q* sample set still omits residue p.  Mirrors SrsaRootPoly.v.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; e=pin_e;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;

check(p < q,                            "p < q so q not in F_p*");
fp_units=1;
for(aa=1, p-1, \
  if(gcd(aa,N)!=1, fp_units=0) \
);
check(fp_units,                         "every residue of F_p* is a unit of N");
check(gcd(p,N)==p,                      "residue p is not a unit of N");

locp=1; locq=1;
for(aa=1, N-1, \
  if(gcd(aa,N)==1, \
    v=ca*aa^da + cb*aa^db + N*aa^20; \
    if(v%p != lift(Mod(aa,p)^da), locp=0); \
    if(v%q != lift(Mod(aa,q)^db), locq=0) \
  ) \
);
check(locp,                             "any-degree invert poly matches X^{d_p} on F_p*");
check(locq,                             "any-degree invert poly matches X^{d_q} on F_q* samples");

check(pin1363_p < pin1363_q,            "1363 p < q");
fp2=1;
for(aa=1, pin1363_p-1, \
  if(gcd(aa,pin1363_N)!=1, fp2=0) \
);
check(fp2,                              "1363 every F_p* residue is a unit of N");
check(pin2491_p < pin2491_q,            "2491 p < q");
fp3=1;
for(aa=1, pin2491_p-1, \
  if(gcd(aa,pin2491_N)!=1, fp3=0) \
);
check(fp3,                              "2491 every F_p* residue is a unit of N");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
