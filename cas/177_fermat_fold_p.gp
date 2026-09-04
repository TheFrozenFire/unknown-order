\\ Fermat fold on F_p*: sum coeffs in each residue class mod (p−1).
\\ Because F_p* is a complete set of samples (p−1 points, fold degree
\\ < p−1), an all-units invert poly has fold_p = X^{d_p} as a
\\ polynomial mod p.  No leftover at the Fermat boundary on this
\\ side.  Adding X^{d_p+(p−1)} changes the fold and does not invert.
\\ Mirrors SrsaRootPoly.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; e=pin_e;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;

check(lift(Mod(2,p)^(p-1))==1,          "Fermat: 2^{p−1}≡1 on F_p*");

Pinv = ca*x^da + cb*x^db + N*x^20;
good=1;
for(r=0, p-2, \
  s=0; \
  for(j=0, 6, s += polcoeff(Pinv, r+j*(p-1))); \
  want = if(r==da, 1, 0); \
  if(s%p != want, good=0) \
);
check(good,                             "fold_p of invert poly is X^{d_p} (mod p)");

Pbad = ca*x^da + cb*x^db + x^(da+p-1);
fold_da=0;
for(j=0, 5, fold_da += polcoeff(Pbad, da+j*(p-1)));
check(fold_da%p == (ca+1)%p,            "X^{d_p+(p−1)} lands in fold class d_p");
miss=lift((Mod(ca*2^da + cb*2^db + 2^(da+p-1), N)^e));
check(miss!=2,                          "binomial + X^{d_p+(p−1)} does not invert unit 2");

\\ 1363 fold of binomial is X^{d_p}
p2=pin1363_p; ca2=pin1363_root_ca; cb2=pin1363_root_cb;
da2=pin1363_inv3_p; db2=pin1363_inv3_q;
P2=ca2*x^da2 + cb2*x^db2;
good2=1;
for(r=0, p2-2, \
  s=polcoeff(P2, r); \
  want = if(r==da2, 1, 0); \
  if(s%p2 != want, good2=0) \
);
check(good2,                            "1363 binomial fold_p is X^{d_p} (mod p)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
