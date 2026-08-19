\\ Okamoto–Uchiyama on N=p²q.  Mirrors OkamotoUchiyama.v.  p=11, q=13.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 11; q = 13; N = p*p*q;
L(x) = (x - 1)\p;
m = 5;
check(lift(Mod(1+p, p*p)^m) == (1 + m*p) % (p*p), "(1+p)^m ≡ 1+m p (mod p²)");
check(L(1 + m*p) == m, "L(1+m p) = m");
check(L(lift(Mod(1+p, p*p)^(m*(p-1)))) == p - m, "L((1+p)^{m(p−1)}) = p−m");
check(L(lift(Mod(1+p, p*p)^(p-1))) == p - 1, "L((1+p)^{p−1}) = p−1");
\\ ratio in F_p recovers m
check(((p-m) * lift(1/Mod(p-1,p))) % p == m, "(p−m)/(p−1) ≡ m (mod p)");

x = 3;
check(gcd(x,p)==1, "randomizer coprime to p");
check(lift(Mod(x, p*p)^(N*(p-1)))==1, "x^{N(p−1)} ≡ 1 (mod p²)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
