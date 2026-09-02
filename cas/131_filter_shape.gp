\\ Twelve partial-root / public-stand-in / filter inroads on Strong RSA.
\\ Mirrors FilterShape.v.  Residual leaf named, not solved.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p=11; q=17; N=p*q; lam=80;

\\ 1. One-sided local root as an integer (not CRT-combined)
check(9^3 == 729,                       "1 9^3 = 729 in Z");
check(lift(Mod(9,p)^3) == 36 % p,       "1 9^3 ≡ 36 (mod p)");
check(lift(Mod(9,N)^3) != 36,           "1 9^3 ≢ 36 (mod N) not global");
check(gcd(9^3-36, N)==11,               "1 gcd(729-36,N)=11 splits");

\\ 2. x = -y
check(lift(Mod(-36,N)^3)==94,           "2 (-36)^3 ≡ 94");
check(94 != 36,                         "2 not a cube root of 36");
check(lift(Mod(36,N)^2) != lift(Mod(-1,N)), "2 36^2 ≢ -1");

\\ 3. Euclid on (y±1, N)
check(gcd(36-1, N)==1,                  "3 gcd(y-1,N)=1");
check(gcd(36+1, N)==1,                  "3 gcd(y+1,N)=1");

\\ 4. Nontrivial 5th root of 1 (λ-sharing e)
check(gcd(5,lam)==5,                    "4 e=5 shares λ");
check(lift(Mod(69,N)^5)==1,             "4 69^5 ≡ 1");
check(gcd(69-1, N)==17,                 "4 gcd(68,N)=17 splits");
check(gcd(69,N)==1,                     "4 69 is a unit");

\\ 5. Public period N+1
check(lift(Mod(2,N)^(N+1))==135,        "5 2^{188} ≡ 135");
check(135 != 2,                         "5 N+1 does not annihilate 2");
check(lift(Mod(2,N)^lam)==1,            "5 λ does annihilate 2");
check(N+1 != lam,                       "5 N+1 is not λ");

\\ 6. Extra output φ
phi=160;
check(phi==(p-1)*(q-1),                 "6 φ=160");
check(N-phi+1 == p+q,                   "6 N-φ+1 = p+q = 28");
check(gcd(11,N)==11,                    "6 recovered prime is a factor");

\\ 7. 2-adic Hensel: v2(y) not divisible by 3
check(valuation(36,2)==2,               "7 v2(36)=2");
check(2 % 3 != 0,                       "7 2 is not a multiple of 3");
check(ispower(36,3)==0,                 "7 36 is not an integer cube");

\\ 8. Locally constant X (function of y mod m)
check(36 % 5 == 1 && 6 % 5 == 1,        "8 36 ≡ 6 (mod 5)");
check(lift(Mod(42,N)^3)==36,            "8 42^3 ≡ 36");
check(36 != 6,                          "8 same x cannot hit both y");

\\ 9. Branch on Jacobi to λ+1
check(kronecker(2,N)==-1,               "9 (2/N)=-1");
check(lift(Mod(2,N)^(lam+1))==2,        "9 2^{81} ≡ 2 λ-type");
check((81-1)%lam==0,                    "9 λ | e-1, not residual");

\\ 10. Public coprimality filter gcd(e, N-1)=1
check(gcd(3, N-1)==3,                   "10 cube e=3 rejected by public filter");
check(gcd(11, N-1)==1,                  "10 e=11 passes public filter");
check(gcd(lift(Mod(36,N)^10)-1, N)==11, "10 that e=11 Miller-splits y");

\\ 11. Low-bit e = 2(y mod 2^k)+1
ee=2*(36 % 8)+1;
check(ee==9,                            "11 e=9 from 36 mod 8");
check(gcd(ee,lam)==1,                   "11 gcd(9,80)=1");
check((ee-1)%lam != 0,                  "11 8 is not a multiple of λ");
x9=lift(Mod(36,N)^9);
check(gcd(x9,N)==1,                     "11 36^9 is a unit");
check(lift(Mod(x9,N)^9)==36,            "11 (36^9)^9 ≡ 36 residual-shaped");

\\ 12. Trace x + x^{-1}
inv36=lift(1/Mod(36,N));
check(inv36==26,                        "12 36^{-1} ≡ 26");
check((36+26)%N==62,                    "12 trace t=62");
check(lift(Mod(62,N)^3)==90,            "12 62^3 ≡ 90 ≠ 36");
check(lcm(p+1,q+1)==36,                 "12 torus order 36, not N+1");
check(36 != N+1,                        "12 torus period is not N+1");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
