\\ 2-of-2 root oracle vs sampled tau.  Mirrors TwoPartyPair.v.
\\ Same numbers as cas/81: 11*17 and 5*23, e=3.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

pA = 11; qA = 17; NA = pA*qA; e = 3; dA = 27;
pB = 5; qB = 23; NB = pB*qB; dB = 15;
Ns = NA*NB;
lA = 80; lB = 44; ls = lcm(lA, lB);
dstar = lift(chinese(Mod(dA, lA), Mod(dB, lB)));
root(c) = lift(chinese(Mod(lift(Mod(c,NA)^dA), NA), Mod(lift(Mod(c,NB)^dB), NB)));

g = 2;
check(gcd(g, Ns)==1, "g unit");
X = 16; Y = 9;
check(gcd(X,Ns)==1 && gcd(Y,Ns)==1, "X,Y units");
check(root((X*Y)%Ns) == (root(X)*root(Y)) % Ns, "root is a homomorphism");
check(lift(Mod(root(X), Ns)^e) == X % Ns, "root(X)^e = X");

\\ using root as next-power on g^{tau^i} forces tau == dstar
tau = 5;
ii = 1;
Ptau = lift(Mod(g, Ns)^(tau^ii));
want = lift(Mod(g, Ns)^(tau^(ii+1)));
got = root(Ptau);
check(got != want, "root(g^{tau^k}) is not g^{tau^{k+1}} for tau != d*");
check(got == lift(Mod(g, Ns)^((tau^ii)*dstar)), "root raises to d*, not tau");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
