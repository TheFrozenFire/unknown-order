\\ Invert-all-units poly: dlog of P(g) recovers k; miller_walk
\\ at e*k-1 splits.  The multiple is read off P, not pin_d as a
\\ module constant.  Mirrors invert_all_units_poly_constructs_factor.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; e=pin_e; d=pin_d; g=pin_g; lam=pin_lam;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;

dlog(base, t) = {
  my(k);
  for(k=0, lam-1, if(lift(Mod(base,N)^k)==(t%N), return(k)));
  -1
};

odd_part(M) = { my(t=M); while(t%2==0, t=t/2); t };
val2(M) = { my(s=0, t=M); while(t%2==0, t=t/2; s++); s };

miller_walk(N, M, a) = {
  my(t, s, cur, nxt, f, i);
  if(M<=0, return(0));
  t = odd_part(M); s = val2(M);
  cur = lift(Mod(a,N)^t);
  for(i=1, s, \
    nxt = lift(Mod(cur,N)^2); \
    if(nxt==1 && cur!=1 && cur!=N-1, \
      f = gcd(cur-1, N); \
      if(1<f && f<N, return(f)) \
    ); \
    cur = nxt \
  );
  0
};

Pmon = x^d;
Pbin = ca*x^da + cb*x^db;
Pg_mon = lift(Mod(subst(Pmon,x,g),N));
Pg_bin = lift(Mod(subst(Pbin,x,g),N));
kmon = dlog(g, Pg_mon);
kbin = dlog(g, Pg_bin);

check(kmon==d,                              "dlog of X^d at g is d");
check(kbin==d,                              "dlog of CRT binomial at g is d");
check(miller_walk(N, e*kmon-1, 2)==p,       "miller_walk at e k_mon - 1 splits");
check(miller_walk(N, e*kbin-1, 2)==p,       "miller_walk at e k_bin - 1 splits");
check(e*d-1==lam,                           "e d - 1 is lambda");
check(lift(Mod(g,N)^d)==Pg_mon,             "X^d(g) = g^d");
check(lift(Mod(g,N)^d)==Pg_bin,             "binomial(g) = g^d");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
