\\ Fiat–Shamir factoring ID = GQ at e=2.  Mirrors GQ.v.
\\ Completeness, odd-Δ extraction of a square root, mixed √1 factors.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p = pin_p; q = pin_q; N = pin_N;
x = 5; z = lift(Mod(x,N)^2); k = 3; c = 4;
t = lift(Mod(k,N)^2);
resp = lift(Mod(k,N) * Mod(x,N)^c);
check(lift(Mod(resp,N)^2) == lift(Mod(t,N)*Mod(z,N)^c), "GQ e=2 complete");

\\ two transcripts, odd challenge difference extracts a square root
c2 = 1;
resp2 = lift(Mod(k,N) * Mod(x,N)^c2);
check((c-c2) % 2 == 1, "Δc is odd");
rinv = lift(1/Mod(resp2,N));
w = lift(Mod(resp,N)*Mod(rinv,N));
check(lift(Mod(w,N)^2) == lift(Mod(z,N)^(c-c2)), "ratio^e = z^{Δc}");
\\ gcd(Δc, 2)=1 and Shamir: w^{2^{-1} mod λ} is a square root of z
lam = lcm(p-1,q-1);
s = lift(Mod(w,N)^lift(1/Mod(c-c2, lam)));
check(lift(Mod(s,N)^2) == z % N, "odd Δ extracts a square root of z");

\\ mixed √1 is a factorization proof, not ZK
mu = lift(chinese([Mod(1,p), Mod(q-1,q)]));
check(lift(Mod(mu,N)^2)==1 && mu != 1 && mu != N-1, "mixed √1");
check(gcd(mu-1, N)==p || gcd(mu-1, N)==q, "mixed √1 factors N");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
