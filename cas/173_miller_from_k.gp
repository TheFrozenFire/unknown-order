\\ An invert-all-units monomial X^k gives M = e k − 1, a multiple of λ.
\\ Miller on that M splits N when the 2-heights mismatch.  k = d,
\\ k = d+λ (odd_part stays, val2 grows), and k = d+2λ (odd_part
\\ changes) all split with base 2.  Not residual-solver ⇒ factor:
\\ writing k wrote a multiple of λ.  Mirrors MillerHeight.v /
\\ SrsaRootPoly.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

oddpart(n) = { while(n%2==0, n = n/2); n };
val2(n) = valuation(n, 2);

miller_factor(N, M, a) = {
  t = oddpart(M); s = val2(M);
  g = lift(Mod(a,N)^t);
  if(g==1, return(0));
  for(i = 1, s, \
    ng = lift(Mod(g,N)^2); \
    if(ng==1, \
      if(g!=1 && g!=N-1, return(gcd(g-1, N)), return(0)) \
    ); \
    g = ng \
  );
  0
};

p=pin_p; q=pin_q; N=pin_N; e=pin_e; d=pin_d; lam=pin_lam;

k0=d; M0=e*k0-1;
check((e*k0)%lam==1,                    "e·d ≡ 1 (mod λ)");
check(M0%lam==0,                        "λ | (e d − 1)");
check(oddpart(M0)==5,                   "odd_part(e d − 1) = 5");
check(val2(M0)==4,                      "v₂(e d − 1) = 4");
f0=miller_factor(N, M0, 2);
check(f0==p || f0==q,                   "Miller on M=ed−1 splits");

k1=d+lam; M1=e*k1-1;
check((e*k1)%lam==1,                    "e·(d+λ) ≡ 1 (mod λ)");
check(M1%lam==0,                        "λ | (e(d+λ) − 1)");
check(oddpart(M1)==oddpart(M0),         "odd_part unchanged at d+λ");
check(val2(M1)>val2(M0),                "v₂ grows at d+λ");
f1=miller_factor(N, M1, 2);
check(f1==p || f1==q,                   "Miller on M=e(d+λ)−1 splits");

k2=d+2*lam; M2=e*k2-1;
check((e*k2)%lam==1,                    "e·(d+2λ) ≡ 1 (mod λ)");
check(M2%lam==0,                        "λ | (e(d+2λ) − 1)");
check(oddpart(M2)!=oddpart(M0),         "odd_part changes at d+2λ");
check(oddpart(M2)==35,                  "odd_part(e(d+2λ)−1) = 35");
g70=gcd(lift(Mod(2,N)^(oddpart(M2)*2))-1, N);
check(g70==p,                           "gcd(2^{35·2}−1, N) = p");
f2=miller_factor(N, M2, 2);
check(f2==p || f2==q,                   "Miller on M=e(d+2λ)−1 splits");

units_k2=1;
for(aa=1, N-1, \
  if(gcd(aa,N)==1, \
    if(lift((Mod(aa,N)^k2)^e)!=aa, units_k2=0) \
  ) \
);
check(units_k2,                         "X^{d+2λ} inverts every unit");

\\ 1363: odd_part of ed−1 is not odd_part(λ) after 2λ; Miller still splits
N2=pin1363_N; e2=pin1363_e; d2=pin1363_d; lam2=pin1363_lam;
p2=pin1363_p; q2=pin1363_q;
M20=e2*d2-1; M22=e2*(d2+2*lam2)-1;
f20=miller_factor(N2, M20, 2);
f22=miller_factor(N2, M22, 2);
check(f20==p2 || f20==q2,               "1363 Miller on ed−1 splits");
check(oddpart(M22)!=oddpart(M20),       "1363 odd_part changes at d+2λ");
check(f22==p2 || f22==q2,               "1363 Miller on e(d+2λ)−1 splits");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
