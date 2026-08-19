\\ Evaluation pairing on mu_n.  Mirrors EvalPairing.v.
\\ N=11*13=143.  n=2 mixed sqrt1; n=3 cube root of 1 mod 13.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 11; q = 13; N = p*q;
\\ mixed sqrt1: 1 mod p, -1 mod q
x2 = lift(chinese(Mod(1,p), Mod(-1,q)));
check(lift(Mod(x2,N)^2) == 1, "mixed sqrt1 is in mu_2");
mu2_ok = 1;
for(k = 0, 11, \
  if(lift(Mod(x2,N)^k) != lift(Mod(x2,N)^(k%2)), mu2_ok = 0) \
);
check(mu2_ok, "eval_pair on mu_2 depends on k mod 2");

\\ primitive cube root mod 13: root of X^2+X+1
\\ 3^2+3+1=13==0
om = 3;
check((om*om + om + 1) % 13 == 0, "omega^2+omega+1=0 mod 13");
check(lift(Mod(om,13)^3) == 1, "omega^3=1");
check(om % 13 != 1, "omega != 1");
mu3_ok = 1;
for(k = 0, 11, \
  if(lift(Mod(om,13)^k) != lift(Mod(om,13)^(k%3)), mu3_ok = 0) \
);
check(mu3_ok, "eval_pair on mu_3 depends on k mod 3");

\\ mu_2 and mu_3 sit in mu_6
check(lift(Mod(x2,N)^6) == 1, "mu_2 subset mu_6");
check(lift(Mod(om,13)^6) == 1, "mu_3 subset mu_6");
check(znorder(Mod(om,13)) == 3, "order of omega is 3, not larger");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
