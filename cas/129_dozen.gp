\\ Twelve algorithm-class inroads on Strong RSA (not the Jacobian leaf).
\\ Mirrors DozenInroads.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p=11; q=17; N=p*q; lam=80;

\\ 1. GRA + Jacobi gate: Jacobi of 2 is -1, so e odd
check(kronecker(2,N) == -1,             "1 Jacobi gate on 2 is -1");
check(81 % 2 == 1,                      "1 then e=81 is odd");

\\ 2. SAGM both x and y in base g=3: y=3^2, x=3^{54}, e=3
g=3; c=2; a=54; ee=3;
y2 = lift(Mod(g,N)^c);
x2 = lift(Mod(g,N)^a);
check(y2 == 9,                          "2 y = g^2 = 9");
check(lift(Mod(x2,N)^ee) == y2,         "2 (g^a)^e ≡ g^c");
check((a*ee - c) % lam == 0,            "2 ae ≡ c (mod ord g)");

\\ 3. Related y, y^2 with gcd(e1,e2)=1
y = lift(Mod(2,N)^15);
x1 = lift(Mod(2,N)^5); e1=3;
x2 = lift(Mod(2,N)^6); e2=5;
check(y == 43,                          "3 y=2^{15}≡43");
check(lift(Mod(x1,N)^e1) == y,          "3 S(y)=(32,3)");
check(lift(Mod(x2,N)^e2) == lift(Mod(y,N)^2), "3 S(y^2)=(64,5)");
check(gcd(e1,e2)==1,                    "3 gcd(3,5)=1 Shamir coprime");
check(lift(Mod(x1,N)^(2*e1)) == lift(Mod(x2,N)^e2), "3 x1^{2 e1}=x2^{e2}");

\\ 4. 5th-power Euler: 5 | 10 = p-1, 32=2^5
check((p-1) % 5 == 0,                   "4 5 | p-1");
check(lift(Mod(32,p)^((p-1)/5)) == 1,   "4 32^{(p-1)/5}≡1 (mod 11)");

\\ 5. one-sided a^{e-1}: e=11, a=2, gcd(2^{10}-1,N)=11
check(gcd(11,lam)==1,                   "5 e=11 coprime to λ");
check((11-1) % lam != 0,                "5 λ does not divide 10");
check(gcd(2^10-1, N)==11,               "5 one-sided 2^{10}-1 splits");

\\ 6. short e: 3 vs 81
check(3 < 4,                            "6 e=3 short vs N^{1/4}~3.7");
check(81 > 4,                           "6 e=81 not short");

\\ 7. bounded advice on N
adv_small = N % 2;
adv_split = N / 17;
check(adv_small == 1 && gcd(adv_small,N)==1, "7 1-bit advice N mod 2 does not split");
check(adv_split == 11 && gcd(adv_split,N)==11, "7 advice N/17 splits");

\\ 8. Blum N=11*23=253, λ=110=2*5*11
Nb=11*23; lamb=lcm(10,22);
check(11%4==3 && 23%4==3,               "8 both Blum");
check(lamb==110,                        "8 λ=110");
check(gcd(5,lamb)==5 && 2*5+1==11 && Nb%11==0, "8 e=5 names p=11");
check(gcd(11,lamb)==11 && 2*11+1==23 && Nb%23==0, "8 e=11 names q=23");

\\ 9. census: every unit is a cube (e=3 permutation)
units=0; cubes=0;
for(yy=1, N-1, \
  if(gcd(yy,N)==1, \
    units++; \
    found=0; \
    for(xx=1, N-1, if(gcd(xx,N)==1 && lift(Mod(xx,N)^3)==yy, found=1)); \
    if(found, cubes++) \
  ) \
);
check(units==160,                       "9 φ(187)=160");
check(cubes==160,                       "9 every unit has a residual e=3 witness");

\\ 10. GQ extract is residual (42,3,36), not a factor
check(lift(Mod(42,N)^3)==36,            "10 extracted root is residual cube");
check(gcd(42,N)==1,                     "10 extract does not split N");

\\ 11. integer polynomial in N: N ≡ q (mod p-1)
check(N % (p-1) == q % (p-1),           "11 187 ≡ 17 (mod 10)");
check(gcd(N-1, p-1)==2,                 "11 gcd(186,10)=2");

\\ 12. gcd(e-1, λ) proper: e=11, gcd(10,80)=10
check(gcd(10, lam)==10,                 "12 gcd(e-1,λ)=10");
check(10 > 2 && 10 < lam,               "12 proper, not 2 and not λ");
check(lam % 10 != 0 || 10 != lam,       "12 λ does not equal 10");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
