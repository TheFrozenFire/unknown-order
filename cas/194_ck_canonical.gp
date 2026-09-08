\\ Binomial + c K agrees with the binomial on F_q* minus p
\\ (K vanishes there).  Extra at residue p is c K(p).  This is
\\ agreement in F_q[X], not invert-all-units on N.  Mirrors
\\ SrsaRootPoly.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;
K=0; for(j=0, q-2, K += p^j * x^(q-2-j));
P=ca*x^da + cb*x^db;
Q=P+5*K;
ag=1;
for(aa=1, q-1, \
  if(aa!=p, if(lift(Mod(subst(Q,x,aa)-subst(P,x,aa),q))!=0, ag=0)) \
);
check(ag,                               "binomial+5K ≡ binomial on F_q* minus p");
ex=lift(Mod(subst(Q,x,p)-subst(P,x,p),q));
check(ex==lift(Mod(5*subst(K,x,p),q)),  "extra at p is 5 K(p)");
check(ex!=0,                            "extra at p nonzero for c=5");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
