\\ d* is an unassembled trapdoor, not ZK.  Iterated shared_dec is g^{d*^k}.
\\ Mirrors SharedKey.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

pA = 11; qA = 17; NA = pA*qA; e = 3; dA = 27; lA = 80;
pB = 5; qB = 23; NB = pB*qB; dB = 15; lB = 44;
Ns = NA*NB; ls = lcm(lA, lB);
dstar = lift(chinese([Mod(dA, lA), Mod(dB, lB)]));
check((e*dstar) % lA == 1, "d* inverts e on λ_A");
check((e*dstar) % lB == 1, "d* inverts e on λ_B — assembling it decrypts Bob");
check((e*dstar - 1) % ls == 0, "e d* − 1 is a multiple of λ*");
g = 2;
check(gcd(g, Ns)==1, "base is a unit");
check(lift(Mod(g, Ns)^(e*dstar - 1))==1, "e d* − 1 annihilates units of N*");

\\ iterated CRT-decrypt is the power map
dec_loc(c) = lift(chinese([Mod(lift(Mod(c,NA)^dA), NA), Mod(lift(Mod(c,NB)^dB), NB)]));
acc = g % Ns;
crs_ok = 1;
for(k = 0, 4, \
  want = lift(Mod(g, Ns)^(dstar^k)); \
  if(acc != want, crs_ok = 0); \
  acc = dec_loc(acc) \
);
check(crs_ok, "iterated shared_dec = g^{d*^k} for k=0..4");
s1 = dec_loc(g % Ns);
check(lift(Mod(s1, Ns)^e) == g % Ns, "first SRS element^e = g");
s0 = g % Ns;
chain_ok = 1;
for(k = 0, 3, \
  nxt = dec_loc(s0); \
  if(lift(Mod(nxt, Ns)^e) != s0, chain_ok = 0); \
  s0 = nxt \
);
check(chain_ok, "each next SRS element^e equals the previous");

\\ uniqueness: two d* differ by a multiple of λ*
d2 = dstar + ls;
check((d2 - dstar) % ls == 0, "d* unique modulo λ*");
s1 = lift(Mod(g, Ns)^dstar);
check(lift(Mod(s1, Ns)^e) == g % Ns, "s1 is an RSA solution for g at this e");
check(lift(Mod(g, Ns)^(ls+1)) == g % Ns, "(g, λ*+1) is a different strong-RSA witness");
check(s1 != g % Ns, "the e-th root is not the λ*+1 witness");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
