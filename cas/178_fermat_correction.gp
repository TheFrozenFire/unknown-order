\\ Fermat correction p(X^{q−1}−1) is 0 on units of N (0 mod p and
\\ 0 mod q by Fermat on F_q*), so binomial + p(X^{q−1}−1) inverts
\\ every unit and has degree q−1.  The new coeff is p, which splits.
\\ N-multiples do not hide a splitting gcd.  A unit coefficient on
\\ (X^{q−1}−1) misses F_p*.  Mirrors SrsaRootPoly.v.  Probe names
\\ avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; e=pin_e;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;

units_ok=1;
for(aa=1, N-1, \
  if(gcd(aa,N)==1, \
    v=ca*aa^da + cb*aa^db + p*(aa^(q-1)-1); \
    if(lift((Mod(v,N)^e))!=aa, units_ok=0) \
  ) \
);
check(units_ok,                         "binomial + p(X^{q−1}−1) inverts every unit");
Pfer=ca*x^da + cb*x^db + p*(x^(q-1)-1);
check(poldegree(Pfer)==q-1,             "Fermat-window degree is q−1");
check(gcd(p,N)==p,                      "coeff of X^{q−1} is p, splits");
check(gcd(-p,N)==p,                     "constant −p splits too");
check(gcd(ca+N,N)==gcd(ca,N),           "N-multiples do not hide gcd");
check(gcd(ca,N)==q,                     "CRT coeff still splits");

miss2=lift((Mod(ca*2^da + cb*2^db + 2*(2^(q-1)-1), N)^e));
check(miss2!=2,                         "binomial + 2(X^{q−1}−1) does not invert unit 2");
check(lift(Mod(2,p)^(q-1))!=1,          "X^{q−1}≢1 on F_p*");

p2=pin1363_p; q2=pin1363_q; N2=pin1363_N; e2=pin1363_e;
ca2=pin1363_root_ca; cb2=pin1363_root_cb;
da2=pin1363_inv3_p; db2=pin1363_inv3_q;
u2=1;
for(aa=1, N2-1, \
  if(gcd(aa,N2)==1, \
    v=ca2*aa^da2 + cb2*aa^db2 + p2*(aa^(q2-1)-1); \
    if(lift((Mod(v,N2)^e2))!=aa, u2=0) \
  ) \
);
check(u2,                               "1363 binomial + p(X^{q−1}−1) inverts every unit");
check(gcd(p2,N2)==p2,                   "1363 Fermat coeff splits");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
