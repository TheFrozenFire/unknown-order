\\ CAS witnesses -- LLX non-membership and Guillou-Quisquater.
\\ Mirrors Accumulator.v (llx_*) and GQ.v.
\\ N = 11*19 = 209, lambda = lcm(10,18) = 90.
\\ PARI: `x` is the polynomial variable; `theta` is reserved. Single-line
\\ check() -- this gp treats a bare newline as end-of-input.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 11; q = 19; N = p*q; lam = lcm(p-1, q-1);
check(N == 209 && lam == 90, "RSA toy N=209, lambda=90");

g = 3;
check(gcd(g, N) == 1, "g=3 is a unit");

\\ ----- LLX completeness: A = g^th, a*th + b*xx = 1, B = g^b ----------
th = 35;
xx = 4;
check(gcd(xx, th) == 1, "xx=4 is not a member of {5,7}");
aa = 3; bb = -26;
check(aa*th + bb*xx == 1, "Bezout 3*35 + (-26)*4 = 1");
A = lift(Mod(g, N)^th);
B = lift(Mod(g, N)^bb);
check((lift(Mod(A, N)^aa) * lift(Mod(B, N)^xx)) % N == g % N, "LLX complete: A^a B^x = g");

\\ ----- LLX extract (negative exponent): th=3, a=1, xx=7 ---------------
\\ A = g^3, B^7 = g^{-2}, gcd(7, 1-3)=1.  7 invertible mod lambda.
the = 3; ae = 1; xe = 7;
check(gcd(xe, 1 - ae*the) == 1, "extract hyp: gcd(x, 1-a*th)=1");
Ae = lift(Mod(g, N)^the);
ginv = lift(1/Mod(g, N));
Be = lift(Mod(g, N)^((-(ae*the - 1)) * lift(1/Mod(xe, lam)) % lam));
check((lift(Mod(Ae, N)^ae) * lift(Mod(Be, N)^xe)) % N == g % N, "extract witness: A^a B^x = g");
check(lift(Mod(Be, N)^xe) == lift(Mod(ginv, N)^(ae*the - 1)), "B^x = ginv^{a*th-1}");
wroot = lift(Mod(g, N)^lift(1/Mod(xe, lam)));
check(lift(Mod(wroot, N)^xe) == g % N, "an x-th root of g exists (via lambda)");

\\ ----- Peng-Bao: member still forges a non-membership witness ---------
xmem = 7;
check(th % xmem == 0, "7 divides th=35 (a member)");
check(gcd(xmem, lam) == 1, "gcd(7, lambda)=1 so Bezout3 exists");
apb = lam; bpb = 13 + lam;
Bpb = lift(Mod(g, N)^bpb);
check(apb >= 0 && bpb >= 0, "Peng-Bao coefficients nonnegative after lambda-shift");
check((lift(Mod(A, N)^apb) * lift(Mod(Bpb, N)^xmem)) % N == g % N, "Peng-Bao: member 7 still has a non-membership witness");

\\ ----- Trapdoor add: w = A^{x^{-1} mod lambda} -----------------------
At = 3; xt = 7;
check(gcd(xt, lam) == 1, "7 invertible mod lambda");
einv = lift(1/Mod(xt, lam));
check((xt * einv) % lam == 1, "7*13 = 1 (mod 90)");
Wt = lift(Mod(At, N)^einv);
check(lift(Mod(Wt, N)^xt) == At % N, "trapdoor add: w^x = A");

\\ ----- GQ completeness -----------------------------------------------
ee = 5; xs = 3; kk = 2; cc = 3;
zz = lift(Mod(xs, N)^ee);
tt = lift(Mod(kk, N)^ee);
rr = lift(Mod(kk, N) * Mod(xs, N)^cc);
check(lift(Mod(rr, N)^ee) == (tt * lift(Mod(zz, N)^cc)) % N, "GQ complete: r^e = t z^c");

\\ ----- GQ two-transcript extract -------------------------------------
ccp = 1;
rrp = lift(Mod(kk, N) * Mod(xs, N)^ccp);
check(lift(Mod(rrp, N)^ee) == (tt * lift(Mod(zz, N)^ccp)) % N, "GQ second transcript verifies");
check(gcd(cc - ccp, ee) == 1, "gcd(Dc, e)=1");
vinv = lift(Mod(rrp, N)^(-1));
vv = (rr * vinv) % N;
check(lift(Mod(vv, N)^ee) == lift(Mod(zz, N)^(cc - ccp)), "ratio^e = z^Dc");
\\ v^e = z^Dc, want e-th root of z.  1*e + (-2)*Dc = 5-4 = 1
check(1*ee + (-2)*(cc-ccp) == 1, "Shamir Bezout on (e, Dc)");
wex = lift(Mod(zz, N)^1 * Mod(vv, N)^(-2));
check(lift(Mod(wex, N)^ee) == zz % N, "extracted e-th root of z");
check(wex % N == xs % N, "extracted root is the witness xs");

\\ ----- Mixed sqrt1 is a factorization, not ZK ------------------------
mu = lift(chinese(Mod(1,p), Mod(-1,q)));
check(lift(Mod(mu, N)^2) == 1, "mixed sqrt1 squares to 1");
check(mu % N != 1 && mu % N != N-1, "mixed sqrt1 is not +/-1");
gg = gcd(mu - 1, N);
check(gg > 1 && gg < N && N % gg == 0, "gcd(mu-1, N) is a proper factor");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
