\\ Existence of a unit of order λ for N=pq.
\\ F_p* has a generator; CRT of local generators has order lcm(p-1,q-1);
\\ ord_N(a)=lcm(ord_p(a),ord_q(a)); lcm of two orders is again an order.
\\ Mirrors Order.v primitive-root / CRT-of-local-orders.
\\ Probe names avoid the word "fail".
\\ Pin N=11·17=187; extra 11×19 is CAS-only (same class as cas/25).

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N;

check(znorder(Mod(2,p))==p-1,           "2 generates F_11*");
check(znorder(Mod(3,q))==q-1,           "3 generates F_17*");
check(znorder(Mod(2,p))==10,            "ord_11(2)=10");
check(znorder(Mod(3,q))==16,            "ord_17(3)=16");

\\ exponent of F_p* is p-1: X^{p-1}-1 vanishes on units, leading 1
check(Mod(x^(p-1)-1,p) != 0,            "X^{10}-1 is not 0 in F_11[X]");
check(poldegree(x^(p-1)-1)==p-1,        "deg(X^{p-1}-1)=p-1");
check(polcoeff(x^(p-1)-1,0)==-1,        "const of X^{p-1}-1 is -1");
check(polcoeff(x^5-1,p-1)==0,           "deg(X^5-1)=5 < p-1");
check(lift(Mod(2,p)^5)!=1,              "X^5-1 misses a unit of F_11*");

\\ lcm of two orders is an order (pin F_11*): ord(2)=10, ord(3)=5
check(znorder(Mod(3,p))==5,             "ord_11(3)=5");
check(lcm(10,5)==10,                    "lcm(ord 2, ord 3)=10 attained");

\\ CRT of local generators
g=lift(chinese(Mod(2,p), Mod(3,q)));
check(g%p==2,                           "CRT g ≡ 2 (mod 11)");
check(g%q==3,                           "CRT g ≡ 3 (mod 17)");
check(gcd(g,N)==1,                      "CRT g is a unit of Z/NZ");
check(znorder(Mod(g,N))==lcm(p-1,q-1),  "ord_N(g)=lcm(p-1,q-1)=λ");
check(lcm(p-1,q-1)==80,                 "λ(187)=80");

\\ pin unit 3 already attains λ
check(znorder(Mod(3,N))==80,            "pin: ord(3)=λ");
check(lcm(znorder(Mod(3,p)), znorder(Mod(3,q)))==80, "ord_N(3)=lcm of locals");

\\ ord_N = lcm(ord_p, ord_q) on several units
ordlcm(a) = lcm(znorder(Mod(a,p)), znorder(Mod(a,q)));
check(znorder(Mod(2,N))==ordlcm(2),     "ord_N(2)=lcm of locals");
check(znorder(Mod(36,N))==ordlcm(36),   "ord_N(36)=lcm of locals");
check(znorder(Mod(42,N))==ordlcm(42),   "ord_N(42)=lcm of locals");
check(znorder(Mod(N-1,N))==ordlcm(N-1), "ord_N(-1)=lcm of locals");

\\ extra modulus 11×19: a CRT generator attains λ
q2=19; N2=p*q2;
g2=lift(chinese(Mod(2,p), Mod(2,q2)));
check(znorder(Mod(2,q2))==q2-1,         "2 generates F_19*");
check(znorder(Mod(g2,N2))==lcm(p-1,q2-1), "11×19 CRT generator attains λ");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
