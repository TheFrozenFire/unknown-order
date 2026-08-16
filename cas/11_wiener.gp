\\ CAS witnesses — Wiener: short d makes e/N a continued-fraction convergent of k/d.
\\ Mirrors Wiener.v (phi-form: e d = 1 + k phi).
\\ Constructed instance: p=587, q=823, d=7 < (1/3) N^{1/4}.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 587; q = 823;
check(isprime(p) && isprime(q),         "587 and 823 prime");
N = p*q; phi = (p-1)*(q-1);
d = 7;
check(gcd(d, phi) == 1,                 "d coprime to phi");
e = lift(1/Mod(d, phi));
check((e*d) % phi == 1,                 "e = d^{-1} (mod phi)");
k = (e*d - 1) / phi;
check(e*d == 1 + k*phi,                 "ed = 1 + k phi");
check(k < e,                            "d < phi ⇒ k < e  (small_d_small_k)");
check(N - phi == p + q - 1,             "N − phi = p+q−1");

\\ integer basin: |ed − k N| * 2 d < N
num = abs(e*d - k*N);
check(num == k*(p+q-1) - 1,             "numerator identity");
check(num * 2 * d < N,                  "in Wiener basin |ed−kN| 2d < N");

\\ continued fractions recover k/d
cf = contfrac(e/N);
found = 0;
for(i = 1, #cf, \
  pq = contfracpnqn(vector(i, j, cf[j])); \
  kk = pq[1,1]; dd = pq[2,1]; \
  if(dd == d && kk == k, found = 1) \
);
check(found == 1,                       "k/d is a convergent of e/N");

\\ conservative integer trigger 18 d^3 < N
check(18 * d * d * d < N,               "wiener_small_d trigger");

\\ large-d contrast: the lambda-inverse of e=65537 is not Wiener-small
e2 = 65537;
check(gcd(e2, phi) == 1,                "65537 coprime to this phi");
d2 = lift(1/Mod(e2, phi));
check(18 * d2 * d2 * d2 > N,            "full-size d is not Wiener-small");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
