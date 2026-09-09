\\ Invert-all-units structure off pin 187: sharp window, Fermat
\\ folds, leftover kernel, N|c.  N=13*19=247, λ=36, e=5,
\\ gcd(5,36)=1, d_q=11 < 17=q−2, 2^{d_q e} ≢ 2 (mod p).
\\ Mirrors short_root_poly_coeff_splits,
\\ no_root_poly_below_dq,
\\ invert_all_units_folds_local_monomials,
\\ leftover_monic_is_geo_kernel,
\\ leftover_kernel_span_mod_q,
\\ invert_all_units_plus_c_kernel_iff.
\\ Pin 187 stays cas/165–197.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p=13; q=19; N=p*q; e=5; lam=lcm(p-1,q-1);
da=lift(Mod(e,p-1)^(-1)); db=lift(Mod(e,q-1)^(-1));
ca=q*lift(Mod(q,p)^(-1)); cb=p*lift(Mod(p,q)^(-1));
P=ca*x^da + cb*x^db;
K=0; for(j=0, q-2, K += p^j * x^(q-2-j));

check(N==247,                           "N=13*19=247");
check(lam==36,                          "lambda=36");
check(gcd(e,lam)==1,                    "gcd(5,36)=1");
check(da==5 && db==11,                  "local inverses d_p=5 d_q=11");
check(db < q-2,                         "d_q < q-2");
check(lift(Mod(2,p)^(db*e))!=2,         "2^{d_q e} ≢ 2 (mod p)");
check((-1)%q != 0,                      "q does not divide -1");

\\ Sharp window: CRT binomial sits at deg = d_q < q-2, inverts, splits.
check(poldegree(P)==db,                 "CRT binomial deg = d_q");
check(gcd(ca,N)==q,                     "coefficient ca splits");
check(gcd(cb,N)==p,                     "coefficient cb splits");
units_ok=1;
for(aa=1, N-1, \
  if(gcd(aa,N)==1, \
    if(lift(Mod(subst(P,x,aa),N)^e)!=aa, units_ok=0) \
  ) \
);
check(units_ok,                         "binomial inverts every unit");
check(lift(Mod(2,N)^da)^e != 2,         "X^{d_p} does not invert unit 2");

\\ Fermat folds of the binomial are the local inverse monomials.
fp=1;
for(r=0, p-2, \
  cs=0; for(j=0, 12, cs += polcoeff(P, r+j*(p-1))); \
  want=if(r==da, 1, 0); \
  if(cs%p != want, fp=0) \
);
check(fp,                               "fold_p is X^{d_p}");
fq=1;
for(r=0, q-2, \
  cs=0; for(j=0, 12, cs += polcoeff(P, r+j*(q-1))); \
  want=if(r==db, 1, 0); \
  if(cs%q != want, fq=0) \
);
check(fq,                               "fold_q is X^{d_q}");
crt=lift(chinese(Mod(da,p-1), Mod(db,q-1)));
check(crt==lift(Mod(e,lam)^(-1)),       "CRT(d_p, d_q) is e^{-1} mod λ");

\\ Leftover kernel: unique monic of deg q-2 vanishing on F_q* \\ {p}.
check(poldegree(K)==q-2,                "K has degree q-2");
check(pollead(K)==1,                    "K is monic");
van=1;
for(a=1, q-1, \
  if(a!=p && subst(K,x,a)%q != 0, van=0) \
);
check(van,                              "K vanishes on F_q* minus p");
check((subst(K,x,p)*(q-p))%q==1,        "K(p) inverse is q-p");
K2=K+q*x^3;
same=1;
for(i=0, q-2, if(polcoeff(K2,i)%q != polcoeff(K,i)%q, same=0));
check(same,                             "K + q X^3 ≡ K (mod q)");
check(pollead(2*K)%q!=1,                "2K is not monic mod q");

\\ N|c: binomial + c K inverts every unit iff N | c.
y=p+q;
check(lift(Mod(subst(P+p*K,x,y),N)^e)!=y, "binomial+pK misses p+q");
check(lift(Mod(subst(P+q*K,x,2),N)^e)!=2, "binomial+qK misses unit 2");
okN=1;
for(yy=1, N-1, \
  if(gcd(yy,N)==1, if(lift(Mod(subst(P+N*K,x,yy),N)^e)!=yy, okN=0)) \
);
check(okN,                              "binomial+N K inverts every unit");
check(subst(K,x,2)%p == lift(Mod(2,p)^(q-2)), "K(2) ≡ 2^{q-2} (mod p)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
