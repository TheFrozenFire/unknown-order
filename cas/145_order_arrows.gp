\\ Named arrows: Order → residual Strong RSA (invert in <y>);
\\ leftover/order + KeyGen mismatch → Factor; matching local orders
\\ do not split.  Mirrors Hardness.v / SrsaOrderArrows.v.
\\ Residual leaf named, not Problem_Factor without mismatch.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

\\ --- Order then invert on N=187 (equality / multiply, no gcd) ---
p=11; q=17; N=p*q; y=36; e=3; d=27; k=40;
check(znorder(Mod(y,N)) == k,           "is_order: ord(y)=40");
check((e*d) % k == 1,                   "3·27 ≡ 1 (mod 40): inverse in <y>");
check(lift(Mod(y,N)^d) == 42,           "x = y^{e^{-1} mod ord} ≡ 42");
check(lift(Mod(42,N)^e) == y,           "Order→sRSA: 42^3 ≡ 36");
check(e%2==1 && gcd(e,80)==1 && (e-1)%80!=0, "residual-shaped e (odd, coprime to λ, λ ndiv e-1)");
check(gcd(lift(Mod(y,N)^k)-1, N) == N,  "equality y^{ord}≡1: gcd=N, no proper factor");

\\ --- mismatch: leftover x (and y) one-sided k=5 splits 187 ---
x=42;
check(lift(Mod(x,p)^5)==1,              "mismatch: x^5 ≡ 1 (mod p)");
check(lift(Mod(x,q)^5)!=1,              "mismatch: x^5 ≢ 1 (mod q)");
check(gcd(lift(Mod(x,N)^5)-1, N)==11,   "leftover x + mismatch → factor 11");
check(gcd(lift(Mod(y,N)^5)-1, N)==11,   "order of y + mismatch k=5 → factor 11");

\\ --- mismatch pin 77: leftover x=2, k=3 ---
Ns=7*11;
check(lift(Mod(2,7)^3)==1,              "77 mismatch: 2^3 ≡ 1 (mod 7)");
check(lift(Mod(2,11)^3)!=1,             "77 mismatch: 2^3 ≢ 1 (mod 11)");
check(gcd(lift(Mod(2,Ns)^3)-1, Ns)==7,  "77 leftover x + mismatch → factor 7");

\\ --- matching local orders on N=247: same k does not split ---
p2=13; q2=19; N2=p2*q2; x2=179; y2=69;
check(znorder(Mod(x2,p2))==6 && znorder(Mod(x2,q2))==6, "247 matching: ord_p(x)=ord_q(x)=6");
check(lift(Mod(x2,p2)^5)!=1,            "247: x^5 ≢ 1 (mod p) — 6 does not divide 5");
check(lift(Mod(x2,q2)^5)!=1,            "247: x^5 ≢ 1 (mod q) — not one-sided");
check(gcd(lift(Mod(x2,N2)^5)-1, N2)==1, "247 matching: gcd(x^5-1,N)=1, not a proper factor");
check(lift(Mod(x2,p2)^6)==1 && lift(Mod(x2,q2)^6)==1, "247: x^6 ≡ 1 both sides (two-sided annihilator)");
check(gcd(lift(Mod(x2,N2)^6)-1, N2)==N2, "247: gcd(x^6-1,N)=N, not a proper factor");
check(lift(Mod(x2,N2)^5)==y2,           "247 leftover invert 179^5 ≡ 69 still holds");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
