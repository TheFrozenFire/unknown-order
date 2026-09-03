\\ Twelve arith / peel-gap / modulus-shape inroads on Strong RSA.
\\ Mirrors ArithShape.v.  Residual leaf named, not solved.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; lam=pin_lam;

\\ 1. Newton cube step in (Z/NZ)
inv3 = lift(1/Mod(3,N));
check(inv3==125,                        "1 3^{-1} ≡ 125");
check((3*125)%N==1,                     "1 3*125 ≡ 1");
nxt = (38 * 125) % N;
check(nxt==75,                          "1 Newton from 1 lands on 75");
check(lift(Mod(75,N)^3)==3,             "1 75^3 ≡ 3 not 36");

\\ 2. e | (y-1)
check((35 % 5)==0,                      "2 5 | 35");
check((35 % 7)==0,                      "2 7 | 35");
check(gcd(5,lam)==5,                    "2 e=5 shares λ");
check(gcd(7,lam)==1,                    "2 e=7 coprime to λ");
check(lift(Mod(60,N)^7)==36,            "2 60^7 ≡ 36 residual-shaped");
check(gcd(60,N)==1,                     "2 60 is a unit");

\\ 3. x=y with e = ord(y)+1
check(znorder(Mod(36,N))==40,           "3 ord(36)=40");
check(lift(Mod(36,N)^41)==36,           "3 36^{41} ≡ 36");
check(gcd(41,lam)==1,                   "3 gcd(41,80)=1");
check((41-1)%lam != 0,                  "3 40 is not a multiple of λ");
check(gcd(lift(Mod(36,N)^40)-1, N)==N,  "3 period of y does not split");

\\ 4. Fermat-on-the-witness gcd(x-y, N)
check(gcd(42-36, N)==1,                 "4 gcd(42-36,N)=1 no split");

\\ 5. Takagi N=p^2 q Hensel tape
Nt = 3*3*5; lamt = lcm(3*2, 4);
check(Nt==45,                           "5 N=9*5=45");
check(lamt==12,                         "5 λ=lcm(6,4)=12");
check(lift(Mod(2,9)^6)==1,              "5 Euler on p^2: 2^6 ≡ 1 (mod 9)");
check(gcd(3,Nt)==3 && 3>1 && 3<Nt,      "5 p=3 is a factor of N");

\\ 6. Public scaling x=2y
check(lift(Mod(72,N)^3)==183,           "6 (2y)^3 ≡ 183");
check(183 != 36,                        "6 not a cube root of 36");

\\ 7. e = nextprime(y)
check(isprime(37),                      "7 37 is prime");
check(37 > 36,                          "7 37 > 36");
check(gcd(37,lam)==1,                   "7 gcd(37,80)=1");
x37 = lift(Mod(36,N)^13);
check((37*13)%lam==1,                   "7 37^{-1} ≡ 13 (mod λ)");
check(lift(Mod(x37,N)^37)==36,          "7 (36^{13})^{37} ≡ 36");

\\ 8. Continued fraction of y/N
check(pin_N == 5*pin_y + 7,                  "8 187 = 5*36 + 7");
check(36 == 5*7 + 1,                    "8 36 = 5*7 + 1");
check(7 == 7*1 + 0,                     "8 7 = 7*1");
check(lift(Mod(5,N)^3) != 36,           "8 convergent num 5 is not a root");
check(lift(Mod(26,N)^3)==185,           "8 denominator 26 cubes to 185");
check(185 != 36,                        "8 26 is the inverse, not the root");

\\ 9. Same x, two coprime moduli
N2=pin_247;
check(gcd(N,N2)==1,                     "9 187 and 247 are coprime");
check(lift(Mod(42,N)^3)==36,            "9 42^3 ≡ 36 (mod 187)");
check(lift(Mod(42,N2)^3)==235,          "9 42^3 ≡ 235 (mod 247)");
check(gcd(36,N)==1,                     "9 neither ciphertext splits 187");

\\ 10. Multiprime N=pqr, mixed √1
N3=pin_105;
check(N3==105,                          "10 N=105");
\\ mixed (1, -1, 1) via CRT: x≡1 mod 3, x≡-1 mod 5, x≡1 mod 7
xm = lift(chinese(chinese(Mod(1,3), Mod(4,5)), Mod(1,7)));
check(lift(Mod(xm,N3)^2)==1,            "10 mixed square is 1");
check(xm != 1 && xm != N3-1,            "10 not ±1");
check(gcd(xm-1, N3)>1 && gcd(xm-1,N3)<N3, "10 gcd(x-1,N) proper");

\\ 11. Factored composite e=15
check(15==3*5,                          "11 15=3*5");
check(gcd(15,lam)==5,                   "11 gcd(15,80)=5 shares λ");
check(gcd(15,lam) != 1,                 "11 not residual e");

\\ 12. DL of y in public base 2
found=0;
for(k=0, 40, if(lift(Mod(2,N)^k)==36, found=1));
check(found==0,                         "12 36 is not a power of 2 mod N");
check(znorder(Mod(2,N))==40,            "12 ord(2)=40");
check(znorder(Mod(36,N))==40,           "12 ord(36)=40 same order, different cyclic");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
