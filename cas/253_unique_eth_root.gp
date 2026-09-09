\\ Unique unit e-th roots when gcd(e,λ)=1, off pin 187.
\\ N=7*13=91, λ=lcm(6,12)=12, e=5, gcd(5,12)=1.
\\ Mirrors unique_unit_eth_root_coprime.  Pin 187 e=5 negative
\\ stays cas/237.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p=7; q=13; N=p*q; lam=lcm(p-1,q-1); e=5;
check(gcd(e,lam)==1,                        "gcd(5,12)=1");
check(lam==12,                              "lambda(7,13)=12");

uniq=1;
for(x=1, N-1, \
  if(gcd(x,N)==1, \
    for(z=1, N-1, \
      if(gcd(z,N)==1 && lift(Mod(x,N)^e)==lift(Mod(z,N)^e) && (x%N)!=(z%N), uniq=0) \
    ) \
  ) \
);
check(uniq,                                 "5th roots unique on units of 91");

\\ Negative: gcd(e,λ)≠1 on this N.  e=3, gcd(3,12)=3.
e3=3;
two=0;
for(x=1, N-1, \
  if(gcd(x,N)==1 && lift(Mod(x,N)^e3)==1 && (x%N)!=1, two=1) \
);
check(gcd(e3,lam)!=1,                       "gcd(3,12) is not 1");
check(two,                                  "a non-1 cube root of 1 exists");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
