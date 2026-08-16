\\ CAS witnesses — Pollard p-1: a one-sided annihilator from smooth p-1.
\\ Mirrors PollardP1.v / StrongPrimes.v.
\\ If p-1 | M and a^M ≡ 1 (mod p) but not (mod q), gcd(a^M-1, N) = p.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

lcm_upto(B) = { m = 1; for(i = 2, B, m = lcm(m, i)); m };

\\ p=13, p-1=12=2^2*3 is 6-smooth; q=23, q-1=22=2*11 is not
p = 13; q = 23; N = p*q; B = 6; M = lcm_upto(B); a = 2;
check(N == 299,                         "N = 13*23 = 299");
check(M == 60,                          "lcm(1..6) = 60");
check((p-1) % 1 == 0 && M % (p-1) == 0, "p-1 | M");
check(M % (q-1) != 0,                   "q-1 does not divide M");
check(lift(Mod(a,p)^M) == 1,            "2^60 ≡ 1 (mod 13)  (Fermat on a multiple)");
check(lift(Mod(a,q)^M) != 1,            "2^60 ≢ 1 (mod 23)");
g = gcd(lift(Mod(a,N)^M) - 1, N);
check(g == p,                           "gcd(2^60-1, 299) = 13");

\\ CRT-RSA reading: e*d_p - 1 is the same one-sided handle
e = 7; dp = lift(1/Mod(e, p-1));
check((e*dp) % (p-1) == 1,              "d_p = e^{-1} (mod p-1)");
Mp = e*dp - 1;
check(Mp % (p-1) == 0,                  "e d_p − 1 is a multiple of p-1");
check(lift(Mod(a,p)^Mp) == 1,           "a^{e d_p−1} ≡ 1 (mod p)");
g2 = gcd(lift(Mod(a,N)^Mp) - 1, N);
check(g2 == p || g2 == N,               "short d_p splits or annihilates both (lucky q)");
if(lift(Mod(a,q)^Mp) != 1, check(g2 == p, "short d_p splits when q-side disagrees"));

\\ safe prime refuses this M: p=47=2*23+1, (p-1)/2=23 > B=10
ps = 47; qs = 59; Ns = ps*qs; Bs = 10; Ms = lcm_upto(Bs);
check(isprime(ps) && isprime((ps-1)/2), "47 is safe");
check((ps-1)/2 > Bs,                    "Sophie Germain prime 23 > B");
check(Ms % (ps-1) != 0,                 "lcm(1..10) is not a multiple of 46");
gs = gcd(lift(Mod(2,Ns)^Ms) - 1, Ns);
check(gs != ps,                         "Pollard with this M does not return the safe prime");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
