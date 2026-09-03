\\ KeyGen shape of the period cut: leftover x is a gcd(x^k-1,N)
\\ proper-factor oracle iff local orders mismatch.
\\ Default pin N=11·17=187 (gcd(p-1,q-1)=2) and N=77 split;
\\ extra pin N=13·19=247 (gcd(p-1,q-1)=6) leftover x has matching
\\ local orders and the same gcd is not a proper factor.
\\ Mirrors SrsaPeriod.v.  Residual leaf named, not solved.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

\\ --- mismatch pin 187: leftover x=42, e=3, y=36 ---
p=pin_p; q=pin_q; N=pin_N; lam=pin_lam; y=pin_y; x=pin_x;
check(gcd(p-1, q-1) == 2,               "187 gcd(p-1,q-1)=2");
check(znorder(Mod(x,p)) == 5,           "187 ord_p(x)=5");
check(znorder(Mod(x,q)) == 8,           "187 ord_q(x)=8 mismatch");
check(gcd(lift(Mod(x,N)^5)-1, N) == 11, "187 gcd(x^5-1,N)=11 splits");
check(gcd(lift(Mod(x,N)^8)-1, N) == 17, "187 gcd(x^8-1,N)=17 splits");
check(lift(Mod(x,N)^3) == y,            "187 leftover 42^3 ≡ 36");

\\ --- mismatch pin 77: leftover x=2, e=7, y=51 ---
Ns=pin_77;
check(gcd(6, 10) == 2,                  "77 gcd(p-1,q-1)=2");
check(znorder(Mod(2,7)) == 3,           "77 ord_p(2)=3");
check(znorder(Mod(2,11)) == 10,         "77 ord_q(2)=10 mismatch");
check(lift(Mod(2,Ns)^7) == 51,          "77 leftover 2^7 ≡ 51");
check(gcd(lift(Mod(2,Ns)^3)-1, Ns) == 7,"77 gcd(x^3-1,N)=7 splits");

\\ --- match pin 247: leftover x=179, e=5, y=69, ord=6 both sides ---
p2=pin_247_p; q2=pin_247_q; N2=pin_247; lam2=pin_247_lam; y2=pin_247_y; x2=pin_247_x; e2=pin_247_e;
check(N2 == 247,                        "247 = 13·19");
check(lam2 == 36,                       "λ(247)=36");
check(gcd(p2-1, q2-1) == 6,             "247 gcd(p-1,q-1)=6");
check(gcd(y2, N2) == 1,                 "247 y=69 is a unit");
check(gcd(x2, N2) == 1,                 "247 leftover x=179 is a unit");
check(lift(Mod(x2,N2)^e2) == y2,        "247 179^5 ≡ 69");
check(e2 % 2 == 1,                      "247 e=5 odd");
check(gcd(e2, lam2) == 1,               "247 gcd(5,36)=1 residual-shaped");
check((e2-1) % lam2 != 0,               "247 λ does not divide e-1");
check(znorder(Mod(x2,p2)) == 6,         "247 ord_p(x)=6");
check(znorder(Mod(x2,q2)) == 6,         "247 ord_q(x)=6 matching");
check(znorder(Mod(x2,N2)) == 6,         "247 ord_N(x)=6");
check(gcd(lift(Mod(x2,N2)^5)-1, N2) == 1, "247 gcd(x^5-1,N)=1 no split (same k as 187)");
check(gcd(lift(Mod(x2,N2)^8)-1, N2) == 1, "247 gcd(x^8-1,N)=1 no split");
check(gcd(lift(Mod(x2,N2)^6)-1, N2) == N2, "247 gcd(x^6-1,N)=N no proper factor");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
