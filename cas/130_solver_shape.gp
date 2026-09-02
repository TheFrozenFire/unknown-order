\\ Twelve solver-shape inroads on Strong RSA (how X and E are computed).
\\ Mirrors SolverShape.v.  Residual leaf named, not solved.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p=11; q=17; N=p*q; lam=80;

\\ 1. Monomial x = y^k, k=2: 2e-1 is odd, 40 even, cannot divide
y=36;
check(znorder(Mod(y,N)) == 40,          "1 ord(36)=40");
check(lift(Mod(y,N)^2) == 174,          "1 y^2 ≡ 174");
check(40 % 2 == 0,                      "1 period 40 is even");
check((2*3-1) % 2 == 1,                 "1 2e-1 is odd for e=3");
check((2*3-1) % 40 != 0,                "1 5 is not a multiple of 40");
check(lift(Mod(174,N)^3) != y,          "1 (y^2)^3 is not y");

\\ 2. Inverse x = y^{-1}
inv36 = lift(1/Mod(36,N));
check(inv36 == 26,                      "2 36^{-1} ≡ 26");
check(lift(Mod(inv36,N)^39) == 36,      "2 26^{39} ≡ 36");
check(gcd(39,lam)==1,                   "2 gcd(39,80)=1 residual-shaped");
check((39-1) % lam != 0,                "2 λ does not divide 38");
inv3 = lift(1/Mod(3,N));
check(inv3 == 125,                      "2 3^{-1} ≡ 125");
check(lift(Mod(inv3,N)^79) == 3,        "2 125^{79} ≡ 3");
check(79+1 == lam,                      "2 e+1 = λ on a generator");
check(gcd(67-1,N)==11,                  "2 Miller on λ still splits");

\\ 3. Affine identity (aY+b)^e ≡ Y as a polynomial
check(2^3 - 2 == 6,                     "3 eval(Y^3-Y,2)=6 not 0");
check((-1) % 187 != 0,                  "3 linear coeff -1 not 0 mod N");
check(lift(Mod(42,N)^3)==36,            "3 pointwise const 42 is residual cube");

\\ 4. Two outputs at the same coprime e
nroot=0; nunit=0;
for(xx=0, N-1, \
  if(lift(Mod(xx,N)^3)==36, nroot++; if(gcd(xx,N)==1, nunit++)) \
);
check(nroot==1,                         "4 exactly one cube root of 36");
check(nunit==1,                         "4 that root is a unit (42)");
n1=0;
for(xx=0, N-1, if(gcd(xx,N)==1 && lift(Mod(xx,N)^3)==1, n1++));
check(n1==1,                            "4 unique unit cube root of 1");
check(gcd(42,N)==1,                     "4 42 is a unit");

\\ 5. Franklin-Reiter: small additive related vs residual reduced
check(4^3 == 64 && 5^3 == 125,          "5 integer cubes 64,125 < N");
check(5^3 - 4^3 == 3*1*4*5 + 1,         "5 cube gap formula");
check(64 < N && 125 < N,                "5 small messages, no reduction");
check(42^3 == 74088 && 74088 > N,       "5 residual 42^3 is not < N");
check(ispower(36,3)==0,                 "5 36 is not an integer cube");
check(lift(Mod(41,N)^3)==105,           "5 reduced (42-1)^3 ≡ 105 ≠ 125");

\\ 6. Chaum-blind: y r^e, unblind recovers x, e is protocol
r=2; ee=3; dd=27;
blind = (36 * lift(Mod(r,N)^ee)) % N;
sig = lift(Mod(blind,N)^dd);
rinv = lift(1/Mod(r,N));
unb = (sig * rinv) % N;
check(blind==101,                       "6 blind y r^e ≡ 101");
check(rinv==94 && (r*rinv)%N==1,        "6 r^{-1} ≡ 94");
check(sig==84,                          "6 signer returns x r");
check(unb==42,                          "6 unblind is the cube root");
check(ee==3,                            "6 protocol e does not depend on y");

\\ 7. Jacobi-discrete e in {3,5}
check(kronecker(36,N)==1,               "7 (36/N)=1 square");
check(kronecker(2,N)==-1,               "7 (2/N)=-1");
check(gcd(5,lam)==5,                    "7 e=5 shares λ, not residual");
check(gcd(3,lam)==1,                    "7 e=3 coprime, residual cube");

\\ 8. Extra annihilator M of y
check(lift(Mod(36,N)^40)==1,            "8 36^{40} ≡ 1 short period");
check(gcd(lift(Mod(36,N)^40)-1, N)==N,  "8 gcd is N, no proper factor");
check(gcd(67-1,N)==11,                  "8 λ-quality Miller still splits");

\\ 9. Extra d with ed ≡ 1 (mod λ)
check(3*27-1 == lam,                    "9 ed-1 = λ");
check((3*27)%lam==1,                    "9 d inverts e mod λ");
check(gcd(67-1,N)==11,                  "9 Miller from that annihilator");

\\ 10. Euler inverse modulo N-1, not λ
check(gcd(3, N-1)==3,                   "10 e=3 not invertible mod 186");
check(gcd(11, N-1)==1,                  "10 e=11 invertible mod 186");
check((11*17)%(N-1)==1,                 "10 11^{-1} ≡ 17 (mod 186)");
check(lift(Mod(36,N)^17)==53,           "10 36^{17} ≡ 53");
check(lift(Mod(36,N)^27)==42,           "10 36^{27} ≡ 42 true d");
check(53 != 42,                         "10 wrong modulus does not invert");

\\ 11. CRT-tape: x = CRT(x_p, x_q)
check(42 % 11 == 9,                     "11 42 ≡ 9 (mod p)");
check(42 % 17 == 8,                     "11 42 ≡ 8 (mod q)");
check(lift(chinese(Mod(9,11),Mod(8,17)))==42, "11 CRT recovers 42");
check(gcd(11,N)==11 && 11>1 && 11<N,    "11 combining modulus is a factor");

\\ 12. Miller on e-1 against the challenge y
check(gcd(11,lam)==1,                   "12 e=11 residual-shaped vs λ");
check((11-1)%lam != 0,                  "12 λ does not divide 10");
check(gcd(lift(Mod(36,N)^10)-1, N)==11, "12 gcd(36^{10}-1,N)=11 splits");
check(gcd(lift(Mod(36,N)^2)-1, N)==1,   "12 e=3: gcd(36^2-1,N)=1 cube survives");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
