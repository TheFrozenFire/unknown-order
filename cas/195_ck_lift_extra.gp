\\ Extra of binomial + c K at the unit p+q is c K(p) (mod q).
\\ Nonzero unless q | c.  Mirrors SrsaRootPoly.v.  Probe names
\\ avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; e=pin_e;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;
K=0; for(j=0, q-2, K += p^j * x^(q-2-j));
P=ca*x^da + cb*x^db;
y=p+q;
Q=P+5*K;
ex=lift(Mod(subst(Q,x,y)-subst(P,x,y),q));
check(ex==lift(Mod(5*subst(K,x,p),q)),  "extra at p+q is 5 K(p)");
check(ex!=0,                            "extra at p+q nonzero for c=5");
Qq=P+q*K;
exq=lift(Mod(subst(Qq,x,y)-subst(P,x,y),q));
check(exq==0,                           "qK extra at p+q is 0 mod q");
check(lift((Mod(subst(P,x,y),N)^e))==y, "binomial inverts p+q");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
