\\ Shared decrypt: CRT of local RSA decryptions is c^{d*}.
\\ Mirrors SharedKey.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

pA = 11; qA = 17; NA = pA*qA; e = 3; dA = 27; lA = lcm(10,16);
pB = 5; qB = 23; NB = pB*qB; dB = 15; lB = lcm(4,22);
Ns = NA*NB; ls = lcm(lA, lB);
dstar = lift(chinese([Mod(dA, lA), Mod(dB, lB)]));

m = 42;
check(gcd(m, Ns)==1, "message is a unit of N*");
c = lift(Mod(m, Ns)^e);
decA = lift(Mod(c, NA)^dA);
decB = lift(Mod(c, NB)^dB);
comb = lift(chinese([Mod(decA, NA), Mod(decB, NB)]));
raw = lift(Mod(c, Ns)^dstar);
check(comb == raw, "CRT(local dec) = c^{d*}");
check(comb % Ns == m % Ns, "shared decrypt recovers m");

\\ a different partner gives a different d*
pC = 5; qC = 41; NC = pC*qC; dC = 27; lC = lcm(4,40);
check(gcd(NA, NC)==1, "second partner coprime");
dstar2 = lift(chinese([Mod(dA, lA), Mod(dC, lC)]));
check(dstar != dstar2, "two partners, two d*");
check(dstar % 80 == 27 && dstar2 % 80 == 27, "both ≡ d_A (mod λ_A)");
check(dstar % 44 == 15 && dstar2 % 40 == 27, "each ≡ its partner d (mod λ_B)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
