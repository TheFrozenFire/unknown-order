\\ Unique monic degree q-2 poly vanishing on F_q* minus p is K.
\\ A second monic vanishing poly of that degree differs by a
\\ deg < q-2 poly with q-2 roots, hence is 0 mod q.
\\ Mirrors SrsaRootPoly.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q;
K=0; for(j=0, q-2, K += p^j * x^(q-2-j));
check(poldegree(K)==q-2,                "K has degree q-2");
check(pollead(K)==1,                    "K is monic");

van=1;
for(aa=1, q-1, \
  if(aa!=p, if(lift(Mod(subst(K,x,aa),q))!=0, van=0)) \
);
check(van,                              "K vanishes on F_q* minus p");

K2=K+q*x^3;
check(poldegree(K2)==q-2,               "K + q X^3 still degree q-2");
check(pollead(K2)==1,                   "K + q X^3 still monic");
same=1;
for(i=0, q-2, if(polcoeff(K2,i)%q != polcoeff(K,i)%q, same=0));
check(same,                             "K + q X^3 ≡ K (mod q)");

zero=1;
for(i=0, q-3, \
  cs=0; for(j=0, 4, cs += 0); \
);
Pshort=x^(q-3);
shortdead=1;
for(aa=1, q-1, \
  if(aa!=p, if(lift(Mod(subst(Pshort,x,aa),q))==0, , shortdead=0)) \
);
check(shortdead==0,                     "X^{q-3} does not vanish on F_q* minus p");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
