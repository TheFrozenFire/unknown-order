\\ Paillier neighbour of RSA: (1+N)^m ≡ 1+mN (mod N²).  Mirrors Paillier.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p = pin_p; q = pin_q; N = pin_N; N2 = pin_Nsq;
check(N == pin_N && N2 == pin_Nsq, "N = pin_N, N²=pin_Nsq");

m = 5;
check(lift(Mod(1+N, N2)^m) == (1 + m*N) % N2, "(1+N)^m ≡ 1+mN (mod N²)");
L(x) = (x - 1)\N;
check(L(1 + m*N) == m, "L(1+mN) = m");
check(L(lift(Mod(1+N, N2)^m)) == m, "L((1+N)^m) = m");

\\ order of 1+N on N² is N
check(lift(Mod(1+N, N2)^N) == 1, "(1+N)^N ≡ 1 (mod N²)");

\\ additive homomorphism
m1 = 5; m2 = 7; r1 = 3; r2 = 4;
enc(m, r) = lift(Mod(1+N, N2)^m * Mod(r, N2)^N);
c12 = enc(m1+m2, r1*r2);
cprod = (enc(m1,r1) * enc(m2,r2)) % N2;
check(c12 == cprod, "Enc(m1+m2, r1 r2) = Enc(m1,r1) Enc(m2,r2)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
