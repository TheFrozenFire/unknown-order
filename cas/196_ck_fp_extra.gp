\\ On F_p*, K ≡ X^{q−2}, so extra of binomial + c K at y is
\\ c y^{q−2} (mod p).  Nonzero at unit 2 unless p | c.
\\ Mirrors SrsaRootPoly.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;
K=0; for(j=0, q-2, K += p^j * x^(q-2-j));
P=ca*x^da + cb*x^db;
Q=P+5*K;
ex=lift(Mod(subst(Q,x,2)-subst(P,x,2),p));
check(ex==lift(Mod(5,p)*Mod(2,p)^(q-2)), "extra at 2 is 5·2^{q-2} (mod p)");
check(ex!=0,                            "extra at 2 nonzero for c=5");
Qp=P+p*K;
ex2=lift(Mod(subst(Qp,x,2)-subst(P,x,2),p));
check(ex2==0,                           "pK extra at 2 is 0 mod p");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
