\\ CAS witnesses — Wesolowski is an ell-th root; Pietrzak forgery is low-order.
\\ Mirrors ExpProof.v / Accumulator.v / Presentation.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

\\ ----- RSA carrier: N = 11*19, lambda = lcm(10,18) = 90 ---------------
N = 11*19; lam = lcm(10,18);
check(N == 209 && lam == 90,            "RSA toy N=209, lambda=90");

x = 7; T = 6; ell = 5;
Q = 2^T \ ell; r = 2^T % ell;
y = lift(Mod(x, N)^(2^T));
pi = lift(Mod(x, N)^Q);
check((lift(Mod(pi, N)^ell) * lift(Mod(x, N)^r)) % N == y % N, "Wesolowski verifies on (Z/NZ)*");
check(lift(Mod(pi, N)^ell) == lift(Mod(x, N)^(Q*ell)), "correct pi is an ell-th root");

\\ Known lambda makes Wesolowski trivial as adaptive root: y^{lam} = 1
check(lift(Mod(y, N)^(lam+1)) == y % N, "lambda+1 is an sRSA witness for y");

\\ Pietrzak T=2: y = x^4, true mid = x^2
y4 = lift(Mod(x, N)^4);
mid = lift(Mod(x, N)^2);
check(lift(Mod(mid, N)^2) == y4,        "true midpoint squares to y");

\\ Bad mid: mid * (-1) also squares to y
bad = (mid * (N-1)) % N;
check(lift(Mod(bad, N)^2) == y4,        "bad midpoint (-x^2) also squares to y");
quot = (bad * lift(1/Mod(mid, N))) % N;
check(quot == N-1,                      "quotient is -1 (constructible 2-torsion)");
check(lift(Mod(quot, N)^2) == 1,        "Pietrzak quotient squares to 1");

\\ Accumulator: A |-> A^e, witness is an e-th root
A0 = 3;
e = 5;
A = lift(Mod(A0, N)^e);
check(lift(Mod(A0, N)^e) == A,          "membership witness is an e-th root");
check(lift(Mod(A, N)^(lam+1)) == A % N, "forged witness from lambda is adaptive root");

\\ ----- Cl(Δ) carrier: Δ = -87, order-2 class is constructible ---------
D = -87;
id = qfbred(Qfb(1, D%2, (D%2 - D)/4));
f = Qfb(3,3,8);
check(qfbred(f*f) == id,                "ambiguous form squares to id");
check(qfbred(f*Qfb(3,-3,8)) == id,      "f compose inverse is id");

\\ Pietrzak on Cl: a bad midpoint of order 2 is the ambiguous class
\\ Restricted low-order must not count it as a break.
check(component(f,1) == 3,              "catalog form (3,3,8) is the public 2-torsion");
h = qfbclassno(D);
check(h == 6,                           "h(-87)=6, so odd-order classes exist");
\\ An element of odd order is *not* constructible 2-torsion
g = Qfb(4,3,6);
check(qfbred(g*g) != id,                "a reduced form of odd order is not order 2");
n = 1; gg = qfbred(g);
while(gg != id && n < 20, gg = qfbred(gg*g); n++);
check(n == 3,                           "that form has order 3 (not a Pietrzak 2-torsion break)");

\\ No lambda+1 from D: |D|=87 is not a multiple of the exponent 6
g6 = Qfb(2,1,11);
check(qfbred(g6^87) != id,              "|D| does not annihilate an order-6 class");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
