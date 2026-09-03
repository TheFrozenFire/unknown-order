\\ CRT-RSA d_q twin.  Mirrors CRTRSA.v.  e d_q ≡ 1 (mod q−1).

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p = pin_p; q = pin_q; e = 3; d = 27;
dq = d % (q-1);
check(dq == d % 16, "d_q = d mod (q−1)");
check((e*dq) % (q-1) == 1, "e d_q ≡ 1 (mod q−1)");
check((e*dq - 1) % (q-1) == 0, "e d_q − 1 is a multiple of q−1");
a = 2;
check(lift(Mod(a,q)^(e*dq-1))==1, "2^{e d_q−1} ≡ 1 (mod q)");
N = p*q;
g = gcd(lift(Mod(a,N)^(e*dq-1))-1, N);
check(g == q || g == N, "short d_q splits or annihilates both");
if(lift(Mod(a,p)^(e*dq-1))!=1, check(g==q, "splits when p-side disagrees"));

\\ twin of d_p
dp = d % (p-1);
check((e*dp) % (p-1) == 1, "e d_p ≡ 1 (mod p−1) still");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
