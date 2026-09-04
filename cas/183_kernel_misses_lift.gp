\\ Geometric kernel K = (X^{q−1}−p^{q−1})/(X−p) vanishes on F_q*
\\ minus residue p, not at p.  Binomial + K therefore matches on
\\ the canonical samples and misses the unit p+q.  K ≡ X^{q−2}
\\ (mod p).  Mirrors SrsaRootPoly.v.  Probe names avoid "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; e=pin_e;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;
K=0; for(j=0, q-2, K += p^j * x^(q-2-j));

van=1;
for(aa=1, q-1, \
  if(aa!=p, if(lift(Mod(subst(K,x,aa),q))!=0, van=0)) \
);
check(van,                              "K vanishes on F_q* minus p");
check(lift(Mod(subst(K,x,p),q))!=0,     "K(p)≢0 (mod q)");
k2p=lift(Mod(subst(K,x,2),p));
check(k2p==lift(Mod(2,p)^(q-2)),        "K(2)≡2^{q−2} (mod p)");

y=p+q;
miss=lift((Mod(ca*y^da + cb*y^db + subst(K,x,y), N)^e));
check(miss!=y,                          "binomial + K misses the unit p+q");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
