\\ The short e-th-root window widens from deg ≤ d_q to deg < q−2.
\\ Roots bound on F_q* minus residue p still forces q | (P − X^{d_q}).
\\ CRT binomial plus N X^{12} has deg 12, inverts every unit, and a
\\ coeff still splits.  Trapdoor X^d sits outside.  Fermat appears at
\\ deg = q−1.  Mirrors SrsaRootPoly.v.  Probe names avoid "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; e=pin_e; d=pin_d;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;

check(db < q-2,                         "d_q < q−2");
check(d >= q-2,                         "trapdoor deg is outside deg < q−2");
check(p < q,                            "residue p lies in 1..q−1");

Pbin = ca*x^da + cb*x^db;
Pmid = Pbin + N*x^12;
check(poldegree(Pbin)==db,              "binomial degree is d_q");
check(poldegree(Pmid)==12,              "binomial + N X^{12} has deg 12");
check(12 < q-2,                         "deg 12 is inside the widened window");
check(12 > db,                          "deg 12 is past d_q");

units_mid=1;
for(aa=1, N-1, \
  if(gcd(aa,N)==1, \
    v=ca*aa^da + cb*aa^db + N*aa^12; \
    if(lift((Mod(v,N)^e))!=aa, units_mid=0) \
  ) \
);
check(units_mid,                        "mid-degree poly inverts every unit");
check(gcd(ca,N)==q,                     "mid-degree poly still splits via c_a");
check(gcd(polcoeff(Pmid,12),N)==N,      "X^{12} coeff is 0 mod N");

Q = Pmid - x^db;
qdiv=1;
for(i=0, poldegree(Q), \
  if(polcoeff(Q,i)%q!=0, qdiv=0) \
);
check(qdiv,                             "q | every coeff of P_mid − X^{d_q}");

check(poldegree(x^d)==d,                "deg(X^d)=d");
check(lift(Mod(2,q)^(q-1))==1,          "Fermat at deg = q−1 on F_q*");

\\ same window inequality on the frozen test pins
check(pin1363_inv3_q < pin1363_q-2,     "1363 d_q < q−2");
check(pin1363_d >= pin1363_q-2,         "1363 trapdoor deg is outside");
check(pin2491_inv3_q < pin2491_q-2,     "2491 d_q < q−2");
check(pin2491_d >= pin2491_q-2,         "2491 trapdoor deg is outside");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
