\\ Endomorphisms vs pairing.  Mirrors Endo.v.
\\ Inversion is public (Bezout).  x |-> x^k is a homomorphism.
\\ Using it as next CRS power forces k == tau.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

N = 11*17;
g = 3;
k = 5;
x = 2; y = 9;
endo(t) = lift(Mod(t, N)^k);

check(gcd(g, N)==1, "g unit");
check(gcd(x, N)==1 && gcd(y, N)==1, "x,y units");
check(endo((x*y)%N) == (endo(x)*endo(y)) % N, "power map is a homomorphism");

a = 4;
check(endo(lift(Mod(g,N)^a)) == lift(Mod(g,N)^(a*k)), "endo(g^a) = g^{a k}");
b = 7;
check(lift(Mod(g,N)^(a*k)) != lift(Mod(g,N)^(a*b)), "g^{a k} is not g^{a b} when k != b");

\\ Bezout inverse exists for every unit
inv_ok = 1;
for(u = 1, N-1, \
  if(gcd(u,N)==1, \
    w = lift(1/Mod(u,N)); \
    if((u*w)%N != 1, inv_ok = 0) \
  ) \
);
check(inv_ok, "every unit has a public inverse");

\\ using endo as next power forces k == tau
tau = 5;
ii = 2;
Ptau = lift(Mod(g, N)^(tau^ii));
want = lift(Mod(g, N)^(tau^(ii+1)));
got = lift(Mod(Ptau, N)^k);
check(got == want, "k = tau: endo walks the string");
k2 = 3;
got2 = lift(Mod(Ptau, N)^k2);
check(got2 != want, "k != tau: endo is not the next power");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
