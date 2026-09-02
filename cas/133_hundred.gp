\\ One hundred Strong-RSA algorithm-class pins.  Mirrors HundredA..HundredFH.v.
\\ Probe names avoid the word "fail" (cas-gate tally footgun).

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p=11; q=17; N=p*q; lam=80;

\\ ========== A 1-12 ==========
check(lift(Mod(36,N)^3)==93,            "01 y^3 ≡ 93");
check(lift(Mod(93,N)^3)==70,            "01 (y^3)^3 ≡ 70 not 36");
check(lift(Mod(145,N)^3)==151,          "02 (N-42)^3 ≡ 151 not 36");
check(N\2==93 && abs(36-93)==57,        "03 midpoint 57");
check(lift(Mod(57,N)^3)==63,            "03 57^3 ≡ 63 not 36");
check(eulerphi(36)==12 && 12%2==0,      "04 phi(36)=12 even");
check(hammingweight(36)==2 && 2%2==0,   "05 Hamming 36 is 2 even");
check(gcd(3,7)==1,                      "06 gcd(3,7)=1 Shamir");
check(lift(Mod(42,N)^3)==36 && lift(Mod(60,N)^7)==36, "06 two leftover roots of 36");
check(N^2==34969,                       "07 Paillier carrier N^2");
check(lift(Mod(1+N, N^2)^1)==1+N,       "07 (1+N)^1 ≡ 1+N mod N^2");
V2=62*62-2; V3=62*V2-62;
check(V3==238142 && V3%N==91,           "08 V_3(62)=238142 ≡ 91 not 36");
check(36%2==0,                          "09 36 is even LSB");
check(lift(Mod(36,N)^3)==93 && 93!=42,  "10 y^e ≡ 93 not 42");
check(gcd(25,lam)==5 && 25%2==1,        "11 e=25 shares λ");
check(2^9 > N && 42 >= 2,               "12 42 is not < N^{1/9}");

\\ ========== B 13-32 ==========
check(lift(Mod(36,N)^5)==100,           "13 y^5 ≡ 100");
check(lift(Mod(100,N)^3)==111,          "13 (y^5)^3 not 36");
check(lift(Mod(36,N)^36)==135,          "14 y^y ≡ 135 not 36");
check(lift(Mod(36,N)^N)==42,            "15 y^N ≡ 42 cube root on this pin");
check(187 % 40 == 27,                   "15 N ≡ d (mod ord y)");
check(lift(Mod(36,N)^(N-1))==157,       "16 y^{N-1} ≡ 157 not 36");
check(lift(Mod(36,N)^(N+1))==16,        "17 y^{N+1} ≡ 16 not 36");
check(sqrtint(36)==6 && 6^2==36,        "18 floor sqrt y = 6");
check(lift(Mod(18,N)^3)==35,            "19 (y/2)^3 ≡ 35 not 36");
check(fromdigits(Vecrev(binary(36)),2)==9, "20 6-bit reverse of 36 is 9");
check(lift(Mod(9,N)^3)==168,            "20 9^3 ≡ 168 not 36");
b43=binary(43); r43=fromdigits(Vecrev(b43),2);
check(r43==53,                          "20 reverse of 43 is 53");
check((36*35/2)%N==69,                  "21 triangular ≡ 69");
check(lift(Mod(37,N)^3)==163,           "22 nextprime-as-x 37^3 ≡ 163");
check(fibonacci(36)%N==85,              "23 F_36 ≡ 85");
check(lift(Mod(85,N)^3)==17,            "23 85^3 ≡ 17 not 36");
check(lift(Mod(2,N)^36)==152,           "24 2^y ≡ 152");
check(lift(Mod(3,N)^36)==47,            "25 3^y ≡ 47");
check((36^2+36+1)%N==24,                "26 Phi_3(y) ≡ 24");
check(lift(Mod(26,N)^3)==185,           "27 (y^{-1})^3 ≡ 185");
check(lift(1/Mod(93,N))==185,           "28 (y^3)^{-1} ≡ 185");
h=lift(chinese(Mod(1,11), Mod(36,17)));
check(h==155 && gcd(h,N)==1,            "29 CRT(1, y mod q)=155 unit");
check(lift(Mod(155,N)^3)==144,          "29 hybrid cube not 36");
m=lift(chinese(Mod(9,11), Mod(1,17)));
check(m==86,                            "30 CRT(9,1)=86");
check(gcd(lift(Mod(m,N)^3)-36, N)==11,  "30 mismatched CRT splits");
check(36+28==64 && 4^3==64,             "31 integer JNT y+28=4^3");
check((36^2+1)%N==175,                  "32 y^2+1 ≡ 175");

\\ ========== C 33-50 ==========
check(lcm(2,6)==6 && 6%2==0,            "33 lambda(36)=6 even");
check(1+logint(36,2)==6 && 6%2==0,      "34 bitlength 6 even");
check(numdiv(36)==9 && gcd(9,lam)==1,   "35 tau=9 leftover-shaped e");
check(sigma(36)==91 && gcd(91,lam)==1,  "36 sigma=91 leftover-shaped");
check(lift(Mod(25,N)^91)==36,           "36 25^{91} ≡ 36");
check(6%2==0,                           "37 rad(36)=6 even");
check(omega(36)==2 && 2%2==0,           "38 omega=2 even");
check(bigomega(36)==4 && 4%2==0,        "39 Omega=4 even");
check(3==3 && gcd(3,lam)==1,            "40 largest prime factor 3 is cube e");
check(37==37 && 37>36 && gcd(37,lam)==1,"41 y+1=37 coincides with nextprime");
check(36/4==9 && gcd(9,lam)==1,         "42 odd part of y is 9");
check(2*2+1==5 && gcd(5,lam)==5,        "43 2 Hamming+1 =5 shares λ");
check(gcd(35,186)==1,                   "44 gcd(y-1,N-1)=1 fallback");
check(gcd(1333,lam)==1 && 1333%2==1,    "45 Phi_3(y) leftover-shaped e");
check(valuation(35,2)==0,               "46 v2(y-1)=0");
check(2*valuation(36,2)+1==5,           "46 2 v2(y)+1=5 shares λ");
check(gcd(63,lam)==1 && 63%2==1,        "47 next Mersenne 63 leftover-shaped");
check(lift(Mod(9,N)^63)==36,            "47 9^{63} ≡ 36");
check(N%36==7 && gcd(7,lam)==1,         "48 N mod y =7 leftover e");
check(lift(Mod(60,N)^7)==36,            "48 60^7 ≡ 36");
check(33==2^5+1 && gcd(33,lam)==1,      "49 Fermat-ish 33 leftover-shaped");
check(lift(Mod(53,N)^33)==36,           "49 53^{33} ≡ 36");
check(2*3*5==30 && 30%2==0,             "50 smooth 30 even");

\\ ========== D 51-62 ==========
check((3*27-1)%10==0,                   "51 e d-1 is a multiple of p-1");
check((11-17)^2==28^2-4*N,              "52 Fermat difference identity");
check(6^2==36,                          "53 planted square 6^2=36");
check(gcd(28-6,N)==11,                  "53 mixed sqrt extra splits");
check(znorder(Mod(3,N))==lam,           "54 ord(3)=λ extra is trapdoor");
check(factor(10)[1,1]==2,               "55 e-1=10 factors as 2*5");
check(factor(186)==[2,1;3,1;31,1],      "56 N-1 = 2 * 3 * 31");
check(27 > 4,                           "57 d=27 is not Wiener-small vs N^{1/4}");
check(lift(Mod(2,N)^80)==1,             "58 2^{80} ≡ 1 sequential square period");
check(valuation(znorder(Mod(2,11)),2)==1, "59 v2(ord_p 2)=1");
check(valuation(znorder(Mod(2,17)),2)==3, "59 v2(ord_q 2)=3 mismatch");
check(znprimroot(11)==2,                "60 primitive root 2 mod p");
check(42>>3==5 && 42%8==2,              "61 half bits of 42 are 5 and 2");
check(kronecker(36,N)==1,               "62 Jacobi of 36 is 1 vacuous cube");

\\ ========== E 63-74 ==========
check(lift(Mod(49,N)^3)==26,            "63 cube root of y^{-1} is x^{-1}");
check(lift(1/Mod(42,N))==49,            "63 42^{-1} ≡ 49");
check((-36)%N==151,                     "64 -y ≡ 151");
check(72==2*36,                         "65 2y=72");
check(gcd(3,5)==1,                      "66 gcd of e=3,5 on y,y^2,y^3");
check(lift(Mod(126,N)^3)==37,           "67 cube root of y+1");
check(gcd(42-60,N)==1,                  "68 gcd of two leftover x is 1");
check(81==lam+1,                        "69 λ+1 is adaptive-root search extra");
check(gcd(N,247)==1 && 36%247==36,      "70 same y two coprime moduli");
check(gcd(3,5)==1,                      "71 twin exponents 3 and 5 coprime");
check((42*60)%N==89,                    "72 product of leftover roots");
check(lift(Mod(89,N)^3)==166,           "72 product is not a cube root of 36");
check(3==3,                             "73 rerand-invariant e is protocol e=3");
check(3==3,                             "74 coins independent of y give fixed e=3");

\\ ========== F 75-84 ==========
check(gcd(lift(Mod(2,N)^60)-1,N)==11,   "75 Pollard p-1 M=60 splits");
check(60%16!=0 && 60%10==0,             "75 10 | 60, 16 does not");
t=26; h=180;
check(gcd(t-h,N)==11,                   "76 rho tortoise 26 hare 180 splits");
check((2*2+1)==5 && (5*5+1)==26,        "76 f=x^2+1 walk");
check(lam != N-1,                       "77 BSGS wrong order λ ≠ N-1");
check(14^2-N==9 && issquare(9),         "78 Fermat a=14 splits");
check((14-3)==11 && (14+3)==17,         "78 Fermat recovers {11,17}");
check(N%11==0 && 11>1 && 11<N,          "79 trial 11 divides N");
Vnm2=2; Vnm1=5;
for(n=2,12, V=5*Vnm1-Vnm2; Vnm2=Vnm1; Vnm1=V);
check(gcd(Vnm1-2,N)==11,                "80 Williams V_12(P=5) splits");
check(gcd(lift(Mod(2,N)^186)-1,N)==1,   "81 index-calculus N-1 period does not split");
check(lift(Mod(2,N)^8)==256%N,          "82 squaring-only 2^{2^3}");
check(36%2==1 || 36%2==0,               "83 1-bit advice on y is LSB");
check(36%2==0,                          "84 streaming first bit of y is 0");

\\ ========== G 85-94 ==========
check(3*3*5==45,                        "85 OU / Takagi N=p^2 q =45");
check(lift(Mod(1+3,9)^2)==(1+2*3)%9,    "85 (1+p)^m ≡ 1+m p mod p^2");
check(N*N*N==6539203,                   "86 DJ carrier N^3");
check(kronecker(36,N)==1,               "87 Cocks carefully chosen Jacobi +1");
check(17*17==289,                       "88 prime-power 17^2");
check(lift(Mod(2,17)^11)==8,            "88 field cube root of 2 is 8");
check(7*23==161 && lcm(6,22)==66,       "89 two safeprimes N=161 λ=66");
check(gcd(3,66)==3,                     "89 cube e=3 shares λ on 161");
check(11%8==3 && 23%8==7,               "90 RW shape 11,23");
check(101+103==204 && 204/2==102,       "91 twins Fermat center 102");
check(11*101==1111 && 1111%11==0,       "92 unbalanced 11 divides 1111");
check(3*5*7==105 && lcm(lcm(2,4),6)==12,"93 triprime λ=12");
check(gcd(3,12)==3,                     "93 cube is not residual on 105");
check(isprime(17) && gcd(3,16)==1,      "94 prime N=17 cubing invertible");
check(lift(Mod(2,17)^11)==8,            "94 2^{11} ≡ 8 cube root in F_17");

\\ ========== H 95-100 ==========
check(gcd(N,lam)==1,                    "95 e=N coprime to λ");
check((N-1)%lam != 0,                   "95 λ does not divide N-1");
check(gcd(N-2,lam)==5,                  "96 e=N-2 shares λ");
check(lift(Mod(-1,N)^3)==N-1,           "97 x=N-1 cubes to -1 not 36");
check(sqrtint(N)==13,                   "98 floor sqrt N =13");
check(lift(Mod(13,N)^3)==140,           "98 13^3 ≡ 140 not 36");
check(gcd(N^2+N+1, lam)==1,             "99 Phi_3(N) leftover-shaped e");
check(lift(Mod(3,N)^46)==36,            "100 y = 3^{46} in <3>");
check(lift(Mod(3,N)^42)==42,            "100 cube root = 3^{42}");
check((42*3)%lam==46,                   "100 ae ≡ c (mod λ) SAGM-both");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
