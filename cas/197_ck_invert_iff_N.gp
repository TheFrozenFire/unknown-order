\\ Binomial + c K inverts every unit of N iff N | c.  p|c kills
\\ the F_p* extra but not the missing F_q* sample; q|c kills the
\\ lift extra but not F_p*.  N-multiples are the same function.
\\ Mirrors SrsaRootPoly.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; e=pin_e;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;
K=0; for(j=0, q-2, K += p^j * x^(q-2-j));
P=ca*x^da + cb*x^db;
y=p+q;
check(lift((Mod(subst(P+K,x,y),N)^e))!=y,   "binomial+K misses p+q");
check(lift((Mod(subst(P+p*K,x,y),N)^e))!=y, "binomial+pK misses p+q");
check(lift((Mod(subst(P+q*K,x,2),N)^e))!=2, "binomial+qK misses unit 2");
okN=1;
for(yy=1, N-1, \
  if(gcd(yy,N)==1, if(lift((Mod(subst(P+N*K,x,yy),N)^e))!=yy, okN=0)) \
);
check(okN,                              "binomial+N K inverts every unit");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
