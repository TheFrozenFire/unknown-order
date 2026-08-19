\\ Shared keygen product: two KeyGen-shaped keys, common e, coprime N.
\\ Mirrors satisfies_keygen_product.  Toy sizes, same rulers.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

pA = 11; qA = 17; NA = pA*qA; e = 3; dA = 27;
pB = 5; qB = 23; NB = pB*qB; dB = 15;
Ns = NA*NB;
check(e == 3, "common e");
check(gcd(NA, NB)==1, "no shared prime");
check((e*dA) % lcm(10,16)==1, "A inverts e");
check((e*dB) % lcm(4,22)==1, "B inverts e");
check(gcd(e, lcm(10,16))==1 && gcd(e, lcm(4,22))==1, "e coprime to both λ");
ls = lcm(lcm(10,16), lcm(4,22));
dstar = lift(chinese([Mod(dA, 80), Mod(dB, 44)]));
check((e*dstar) % ls == 1, "combined inverse");
check(!(18*dstar^3 < Ns), "d* is not Wiener-small vs N*");

\\ arity 3: third cofactor 47 (p≡2 mod 3 so e=3 inverts on p−1)
pC = 47; lC = pC-1;
check(isprime(pC), "third cofactor is prime 47");
check(gcd(NA, pC)==1 && gcd(NB, pC)==1, "third cofactor coprime to both");
l3 = lcm(ls, lC);
dC = lift(1/Mod(e, lC));
check((e*dC) % lC == 1, "third local inverse");
d3 = lift(chinese([Mod(dstar, ls), Mod(dC, lC)]));
check((e*d3) % l3 == 1, "arity-3 combined inverse");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
