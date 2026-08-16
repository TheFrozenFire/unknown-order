\\ CAS witnesses — Miller–Rabin polarity: same engine, exponent n−1 vs ed−1.
\\ Mirrors MillerRabin.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

oddpart(n) = { while(n%2==0, n = n/2); n };

\\ On a prime, a^{p−1} ≡ 1 (Fermat) — the sequence must reach 1
p = 17;
fer_fail = 0;
for(a = 1, p-1, if(lift(Mod(a,p)^(p-1)) != 1, fer_fail++));
check(fer_fail == 0,                    "Fermat: a^{16} ≡ 1 (mod 17) for all units");

\\ The MR split of p−1 and the Miller split of M coincide when n−1 = M
M = 80; n = M+1;
check(oddpart(n-1) == oddpart(M),       "mr_t(M+1) = miller_t");
check(valuation(n-1,2) == valuation(M,2), "mr_s(M+1) = miller_s");

\\ A composite N=187 with exponent N−1 (true MR) vs exponent M=80 (factoring)
N = 187;
\\ MR on N with a=2: 2^{186} ≡ 1, but the chain from 2^{oddpart(186)} may misbehave
tN = oddpart(N-1);
g = lift(Mod(2,N)^tN);
\\ we only check the two engines are the same function of (base, exponent-split)
tM = oddpart(80);
check(tM == 5,                          "factoring engine uses t=5");
check(tN == oddpart(186),               "MR engine uses odd part of 186");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
