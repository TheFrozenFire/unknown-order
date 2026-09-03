\\ Determinant pairing on mu_3(Z/NZ)* ≅ C_3 × C_3.
\\ Alternating bilinear and non-degenerate: e(g_p, g_q)=omega_p ≠ 1.
\\ Contrast CAS 157: on cyclic mu_3(F_p*) the alternating pairing is 1.
\\ Trapdoor: local exponents use the factors. Named extra 13×7=91.
\\ Pin kernel is {1}, so the pairing is vacuous there.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 13; q = 7; N = p*q;
om_p = 3; om_q = 2;
g_p = lift(chinese(Mod(om_p, p), Mod(1, q)));
g_q = lift(chinese(Mod(1, p), Mod(om_q, q)));

check(g_p == 29,                          "g_p = CRT(3,1) = 29");
check(g_q == 79,                          "g_q = CRT(1,2) = 79");
check(lift(Mod(g_p, N)^3) == 1,           "g_p^3 ≡ 1 (mod 91)");
check(lift(Mod(g_q, N)^3) == 1,           "g_q^3 ≡ 1 (mod 91)");
check(znorder(Mod(g_p, N)) == 3,          "ord(g_p)=3");
check(znorder(Mod(g_q, N)) == 3,          "ord(g_q)=3");
check(g_p % p == om_p && g_p % q == 1,    "g_p ≡ omega_p (mod p), 1 (mod q)");
check(g_q % p == 1 && g_q % q == om_q,    "g_q ≡ 1 (mod p), omega_q (mod q)");

ker_of(m) = {
  L = List();
  for(x = 1, m-1, if(gcd(x,m)==1 && lift(Mod(x,m)^3)==1, listput(L, x)));
  L
};
ker = ker_of(N);
check(#ker == 9,                          "9 kernel elements");

maxord_ker(L, m) = {
  mx = 1;
  for(i = 1, #L, if(znorder(Mod(L[i], m)) > mx, mx = znorder(Mod(L[i], m))));
  mx
};
check(maxord_ker(ker, N) == 3,            "kernel is not cyclic: max order 3");

exp_p(x) = {
  r = x % p;
  if(r == 1, 0, if(r == om_p, 1, 2))
};
exp_q(x) = {
  r = x % q;
  if(r == 1, 0, if(r == om_q, 1, 2))
};
det(x, y) = lift(Mod(om_p, p)^((exp_p(x)*exp_q(y) - exp_q(x)*exp_p(y)) % 3));

check(det(g_p, g_q) == om_p,              "e(g_p,g_q)=omega_p ≠ 1");
check(det(g_q, g_p) == lift(Mod(om_p,p)^2), "e(g_q,g_p)=omega_p^2 (skew)");
check(det(g_p, g_p) == 1,                 "e(g_p,g_p)=1");
check(det(g_q, g_q) == 1,                 "e(g_q,g_q)=1");

alt_ok(L) = {
  okc = 1;
  for(i = 1, #L, if(det(L[i], L[i]) != 1, okc = 0));
  okc
};
check(alt_ok(ker),                        "e(x,x)=1 on all 9 kernel elements");

bil_ok(L) = {
  okc = 1;
  for(i = 1, #L, for(j = 1, #L, for(k = 1, #L,
    if(det(lift(Mod(L[i]*L[j], N)), L[k]) != lift(Mod(det(L[i],L[k])*det(L[j],L[k]), p)), okc = 0)
  )));
  for(i = 1, #L, for(j = 1, #L, for(k = 1, #L,
    if(det(L[i], lift(Mod(L[j]*L[k], N))) != lift(Mod(det(L[i],L[j])*det(L[i],L[k]), p)), okc = 0)
  )));
  okc
};
check(bil_ok(ker),                        "det pairing is bilinear on the kernel");

n_nz(L) = {
  c = 0;
  for(i = 1, #L, for(j = 1, #L, if(det(L[i], L[j]) != 1, c++)));
  c
};
check(n_nz(ker) > 0,                      "pairing is non-degenerate: some e(x,y)≠1");

Npin = 11*17;
check(#ker_of(Npin) == 1,                 "pin kernel is {1}: pairing vacuous");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
