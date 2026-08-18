\\ Multi-prime: eight √1 on N=pqr, mixed split, λ(pqr) annihilates.
\\ Mirrors MultiPrime.v.  N = 11·13·17.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 11; q = 13; r = 17; N = p*q*r;
check(N == 2431, "N = 11·13·17 = 2431");

nroots = 0;
for(x = 0, N-1, if(lift(Mod(x,N)^2)==1, nroots++));
check(nroots == 8, "exactly eight square roots of 1");

\\ CRT mixed pattern (+1, −1, +1)
chinese_pm = [Mod(1,p), Mod(q-1,q), Mod(1,r)];
xpm = lift(chinese(chinese_pm));
check(lift(Mod(xpm,N)^2)==1, "constructed (+1,−1,+1) squares to 1");
check(xpm % p == 1 && xpm % q == q-1 && xpm % r == 1, "residues match the pattern");
g = gcd(xpm-1, N);
check(g > 1 && g < N && N % g == 0, "mixed root splits N");
check(g % p == 0, "the split includes p (the +1 side)");
check(g % q != 0, "the split excludes q (the −1 side)");

lam = lcm(lcm(p-1, q-1), r-1);
check(lam == 240, "λ(11·13·17) = lcm(10,12,16) = 240");
units_ok = 1;
for(a = 2, 40, \
  if(gcd(a,N)==1 && lift(Mod(a,N)^lam)!=1, units_ok = 0) \
);
check(units_ok, "a^λ ≡ 1 on units a=2..40");

\\ one-sided: M = p-1 annihilates mod p, not mod N
M = p-1; a = 2;
check(lift(Mod(a,p)^M)==1, "2^{10} ≡ 1 (mod 11)");
check(lift(Mod(a,N)^M)!=1, "2^{10} ≢ 1 (mod 2431)");
gs = gcd(lift(Mod(a,N)^M)-1, N);
check(gs > 1 && gs < N, "one-sided period splits pqr");
check(gs % p == 0, "the one-sided split includes p");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
