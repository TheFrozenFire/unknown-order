\\ Unit e-th roots are unique when gcd(e, lam)=1.  Kernel of
\\ 5th-powering is nontrivial (5 | lam): 1 and 69 = g^16.
\\ Mirrors unique_unit_eth_root_from_coprime_e /
\\ pin_e5_fifth_roots_not_unique.  Not residual-solver => factor.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N=pin_N; lam=pin_lam; g=pin_g;

check(gcd(3,lam)==1,                    "gcd(3, lam)=1");
check(gcd(7,lam)==1,                    "gcd(7, lam)=1");
check(gcd(11,lam)==1,                   "gcd(11, lam)=1");
check(gcd(5,lam)==5,                    "gcd(5, lam)=5, shares lam");

u=lift(Mod(g,N)^16);
check(u==69,                            "g^16 is 69");
check(gcd(u,N)==1,                      "69 is a unit");
check(lift(Mod(u,N)^5)==1,              "69^5 is 1");
check(lift(Mod(1,N)^5)==1,              "1^5 is 1");
check(1!=u,                             "1 and 69 are distinct 5th roots of 1");

inj7=1;
for(x=1, N-1, \
  if(gcd(x,N)==1, \
    for(z=x+1, N-1, \
      if(gcd(z,N)==1 && lift(Mod(x,N)^7)==lift(Mod(z,N)^7), inj7=0) \
    ) \
  ) \
);
check(inj7,                             "7th-powering is injective on units");

inj3=1;
for(x=1, N-1, \
  if(gcd(x,N)==1, \
    for(z=x+1, N-1, \
      if(gcd(z,N)==1 && lift(Mod(x,N)^3)==lift(Mod(z,N)^3), inj3=0) \
    ) \
  ) \
);
check(inj3,                             "cubing is injective on units");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
