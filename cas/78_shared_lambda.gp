\\ Shared modulus: λ* = lcm(λ_A, λ_B) and CRT of inverses.
\\ Mirrors SharedKey.v.  N_A=11·17, N_B=5·23, common e=3.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

pA = pin_p; qA = pin_q; NA = pin_N; e = pin_e; dA = pin_d; lA = pin_lam;
pB = 5; qB = 23; NB = pB*qB; dB = 15; lB = lcm(pB-1, qB-1);
Ns = NA*NB; ls = lcm(lA, lB);
check(NA == pin_N && NB == 115, "N_A=pin_N, N_B=115");
check(gcd(NA, NB) == 1, "coprime moduli");
check(lA == pin_lam && lB == 44, "λ_A=pin_lam, λ_B=44");
check(ls == 880, "λ* = lcm(80,44) = 880");
check((e*dA) % lA == 1 && (e*dB) % lB == 1, "local inverses of e");
check((dA - dB) % gcd(lA, lB) == 0, "d_A ≡ d_B (mod gcd(λ_A,λ_B))");
dstar = lift(chinese([Mod(dA, lA), Mod(dB, lB)]));
check(dstar % lA == dA % lA && dstar % lB == dB % lB, "d* CRT of local d");
check((e*dstar) % ls == 1, "e d* ≡ 1 (mod λ*)");

units_ok = 1;
for(a = 2, 40, \
  if(gcd(a,Ns)==1 && lift(Mod(a,Ns)^ls)!=1, units_ok = 0) \
);
check(units_ok, "a^{λ*} ≡ 1 on units a=2..40");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
