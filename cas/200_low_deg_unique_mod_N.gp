\\ Deg < q−1 invert-all-units poly is unique mod N: binomial + N K
\\ has the same coefficients mod N as the CRT binomial, inverts,
\\ and has degree q−2.  p K is a different residue class and misses
\\ the lift.  Mirrors SrsaRootPoly.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; e=pin_e;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;
K=0; for(j=0, q-2, K += p^j * x^(q-2-j));
P=ca*x^da + cb*x^db;
Q=P + N*K;
R=P + p*K;
check(poldegree(Q)==q-2,                "deg(binomial+N K)=q−2 < q−1");
okN=1;
for(yy=1, N-1, \
  if(gcd(yy,N)==1, if(lift((Mod(subst(Q,x,yy),N)^e))!=yy, okN=0)) \
);
check(okN,                              "binomial+N K inverts every unit");
cong=1;
for(i=0, q-2, \
  if(polcoeff(Q,i)%N!=polcoeff(P,i)%N, cong=0) \
);
check(cong,                             "binomial+N K ≡ binomial (mod N)");
y=p+q;
check(lift((Mod(subst(R,x,y),N)^e))!=y, "binomial+p K misses p+q");
diffp=0;
for(i=0, q-2, \
  if(polcoeff(R,i)%N!=polcoeff(P,i)%N, diffp=1) \
);
check(diffp,                            "binomial+p K differs mod N");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
