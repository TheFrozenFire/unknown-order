\\ Unique monic degree q−2 poly vanishing on F_q* minus p is K.
\\ Both monic ⇒ difference has deg < q−2 and q−2 roots, hence 0
\\ mod q.  2K is not monic.  Mirrors SrsaRootPoly.v.  Probe names
\\ avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q;
K=0; for(j=0, q-2, K += p^j * x^(q-2-j));
check(poldegree(K)==q-2,                "K has degree q-2");
check(pollead(K)==1,                    "K is monic");
K2=K+q*x^3;
check(pollead(K2)==1,                   "K + q X^3 still monic");
same=1;
for(i=0, q-2, if(polcoeff(K2,i)%q != polcoeff(K,i)%q, same=0));
check(same,                             "K + q X^3 ≡ K (mod q)");
check(pollead(2*K)==2,                  "2K is not monic");
check(pollead(2*K)%q!=1,                "2K is not monic mod q");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
