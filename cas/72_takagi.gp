\\ Takagi multi-power RSA: N = p²q.  Mirrors Takagi.v.  p=11, q=13.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 11; q = 13; N = p*p*q;
check(N == 1573, "N = 11²·13 = 1573");
check(isprime(p) && isprime(q) && p != q, "distinct odd primes");

lam_p2 = p*(p-1);
lam = lcm(lam_p2, q-1);
phi = p*(p-1)*(q-1);
check(lam_p2 == 110, "λ(p²) = p(p−1) = 110");
check(lam == 660, "λ(p²q) = lcm(110,12) = 660");
check(phi % lam == 0, "λ | φ(p²q)");

\\ Euler on p²
a = 3;
check(gcd(a,p)==1, "3 coprime to 11");
check(lift(Mod(a,p*p)^lam_p2)==1, "3^{λ(p²)} ≡ 1 (mod p²)");
check(lift(Mod(a,N)^lam)==1, "3^λ ≡ 1 (mod N)");

\\ √1 on p² is only ±1
n_pm = 0;
for(x = 0, p*p-1, if(lift(Mod(x,p*p)^2)==1, n_pm++));
check(n_pm == 2, "exactly two √1 mod p²");
check(lift(Mod(1,p*p)^2)==1 && lift(Mod(p*p-1,p*p)^2)==1, "±1 square to 1");

\\ four √1 on N = p²q; mixed (+1 on p², −1 on q) splits
nroots = 0;
for(x = 0, N-1, if(lift(Mod(x,N)^2)==1, nroots++));
check(nroots == 4, "exactly four √1 on p²q (not eight)");
xpm = lift(chinese([Mod(1,p*p), Mod(q-1,q)]));
check(lift(Mod(xpm,N)^2)==1, "constructed (+1,−1) squares to 1");
g = gcd(xpm-1, N);
check(g > 1 && g < N && N % g == 0, "mixed root splits N");
check(g % (p*p) == 0, "the split includes p²");
check(g % q != 0, "the split excludes q");

\\ e d ≡ 1 (mod λ) ⇒ a^{ed} ≡ a (mod p²)
e = 7; d = lift(1/Mod(e, lam));
check((e*d) % lam == 1, "e d ≡ 1 (mod λ)");
check(lift(Mod(a, p*p)^(e*d)) == a % (p*p), "a^{ed} ≡ a (mod p²)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));

