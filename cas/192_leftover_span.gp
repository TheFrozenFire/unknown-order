\\ Any poly of deg < q−1 vanishing on F_q* minus p is a scalar
\\ multiple of K modulo q.  5K vanishes; 5K + X^{q−3} does not;
\\ q-multiples do not change the class.  Mirrors SrsaRootPoly.v.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q;
K=0; for(j=0, q-2, K += p^j * x^(q-2-j));
P=5*K;
van=1;
for(aa=1, q-1, \
  if(aa!=p, if(lift(Mod(subst(P,x,aa),q))!=0, van=0)) \
);
check(van,                              "5K vanishes on F_q* minus p");
check(lift(Mod(subst(P,x,p),q))==lift(Mod(5*subst(K,x,p),q)), "5K(p) = 5 K(p)");
check(lift(Mod(subst(K,x,p),q))!=0,     "K(p) invertible so the scalar is unique");

P2=5*K + x^(q-3);
van2=1;
for(aa=1, q-1, \
  if(aa!=p, if(lift(Mod(subst(P2,x,aa),q))!=0, van2=0)) \
);
check(van2==0,                          "5K + X^{q-3} does not vanish");

P3=5*K + q*x^2;
same=1;
for(i=0, q-2, if(polcoeff(P3,i)%q != polcoeff(P,i)%q, same=0));
check(same,                             "5K + q X^2 ≡ 5K (mod q)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
