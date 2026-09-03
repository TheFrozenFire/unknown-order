\\ CAS witnesses — Rabin-Williams: e=2, Williams primes, unique tweak.
\\ Mirrors QuadResidue.v / RabinWilliams.v.
\\ Textbook pair: p=11 ≡ 3 (mod 8), q=23 ≡ 7 (mod 8), N=253.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p = pin_253_p; q = pin_253_q; N = pin_253;
check(N == pin_253,                     "N = pin_253");
check(p % 8 == 3 && q % 8 == 7,         "Williams shape p≡3, q≡7 (mod 8)");
check(p % 4 == 3 && q % 4 == 3,         "both Blum (≡3 mod 4)");
check(((p-1)/2) % 2 == 1,               "v2(p-1)=1: (p-1)/2 odd");
check(((q-1)/2) % 2 == 1,               "v2(q-1)=1: (q-1)/2 odd");

lam = lcm(p-1, q-1);
check(lam % 2 == 0,                     "λ even");
check(gcd(2, lam) == 2,                 "e=2 is not an RSA exponent");

\\ RSA textbook primes 11,17 are NOT a Williams pair
check(17 % 8 == 1,                      "rsa_test q=17 ≡ 1 (mod 8), not RW");
check(17 % 4 == 1,                      "17 is not even Blum");

\\ sqrt formula p≡3 (mod 4): 5 is QR mod 11
check(kronecker(5,11) == 1,             "5 is QR mod 11");
s = lift(Mod(5,11)^((11+1)/4));
check(s == 4,                           "5^{(11+1)/4} ≡ 4");
check((s*s) % 11 == 5,                  "4^2 ≡ 5 (mod 11)");

\\ -1 is QNR mod Blum primes
check(kronecker(-1, p) == -1,           "(-1/11) = -1");
check(kronecker(-1, q) == -1,           "(-1/23) = -1");
check(kronecker(2, p) == -1,            "(2/11) = -1   (p≡3 mod 8)");
check(kronecker(2, q) == 1,             "(2/23) = +1   (q≡7 mod 8)");

\\ Williams uniqueness: among {±a, ±2a} exactly one is QR mod N
tweaks(a) = [a, -a, 2*a, -2*a];
is_qr_N(y) = kronecker(y, p)==1 && kronecker(y, q)==1;
uniq_fail = 0; n_units = 0;
for(a = 1, N-1, \
  if(gcd(a,N)==1, \
    n_units++; \
    c = 0; \
    T = tweaks(a); \
    for(i = 1, 4, \
      ti = lift(Mod(T[i], N)); \
      if(is_qr_N(ti), c++) \
    ); \
    if(c != 1, uniq_fail++) \
  ) \
);
check(n_units == eulerphi(N),           "counted φ(N) units");
check(uniq_fail == 0,                   "exactly one of {±a,±2a} is QR mod N (exhaustive)");

\\ four square roots of a QR
a0 = 5;
\\ find the unique QR tweak of 5
tw = 0;
for(i = 1, 4, if(is_qr_N(tweaks(a0)[i]), tw = tweaks(a0)[i]));
check(tw != 0,                          "5 has a QR tweak");
sp = lift(Mod(tw, p)^((p+1)/4));
sq = lift(Mod(tw, q)^((q+1)/4));
s1 = lift(chinese(Mod(sp,p), Mod(sq,q)));
s2 = N - s1;
s3 = lift(chinese(Mod(p-sp,p), Mod(sq,q)));
s4 = N - s3;
roots = Set([s1%N, s2%N, s3%N, s4%N]);
check(#roots == 4,                      "four distinct square roots");
rt_ok = 1;
for(i = 1, #roots, if(lift(Mod(roots[i],N)^2) != tw % N, rt_ok = 0));
check(rt_ok == 1,                       "each squares to the tweaked message");

\\ Rabin reduction: plant r, take a non-associated root of r^2, gcd
r = 9;
y = lift(Mod(r,N)^2);
yp = y % p; yq = y % q;
rp = lift(Mod(yp,p)^((p+1)/4));
rq = lift(Mod(yq,q)^((q+1)/4));
t1 = lift(chinese(Mod(rp,p), Mod(rq,q))) % N;
t3 = lift(chinese(Mod(p-rp,p), Mod(rq,q))) % N;
if(t1 != r%N && t1 != (N-r)%N, other = t1, other = t3);
check(other != r%N && other != (N-r)%N, "found a non-associated root of r^2");
g = gcd(other - r, N);
check(g == p || g == q,                 "gcd(s-r, N) is a prime factor");

\\ RW verify: s^2 is one of the four tweaks
H = 5; s = s1;
v = lift(Mod(s,N)^2);
check(v==H%N || v==(-H)%N || v==(2*H)%N || v==(-2*H)%N, \
                                        "rw_verify: s^2 is a tweak of H");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
