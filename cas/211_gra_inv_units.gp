\\ gra_inv of every reduced unit is a modular inverse.  gra_inv of p
\\ returns gcd p.  Mirrors pin_gra_inv_inverts_reduced_unit.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; N=pin_N;

gra_inv(h, NN) = {
  g = gcd(h, NN);
  if(g==1, lift(1/Mod(h,NN)), g)
};

allinv=1;
for(h=1, N-1, \
  if(gcd(h,N)==1, if((gra_inv(h,N)*h)%N!=1, allinv=0)) \
);
check(allinv,                           "gra_inv inverts every reduced unit");
check(gra_inv(p,N)==p,                  "gra_inv of p is gcd p");
check(gra_inv(36,N)*36%N==1,            "gra_inv of pin y is an inverse");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
