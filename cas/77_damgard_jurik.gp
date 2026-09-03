\\ Damgård–Jurik s=2: (1+N)^m ≡ 1+mN+C(m,2)N² (mod N³).  Mirrors DamgardJurik.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p = pin_p; q = pin_q; N = pin_N; N3 = N*N*N;
m = 5; t = m*(m-1)/2;
check(m*(m-1) == 2*t, "C(m,2) is integral");
lhs = lift(Mod(1+N, N3)^m);
rhs = (1 + m*N + t*N*N) % N3;
check(lhs == rhs, "(1+N)^m ≡ 1+mN+C(m,2)N² (mod N³)");

m1 = 5; m2 = 7; r1 = 3; r2 = 4;
enc(mm, r) = lift(Mod(1+N, N3)^mm * Mod(r, N3)^N);
check(enc(m1+m2, r1*r2) == (enc(m1,r1)*enc(m2,r2)) % N3, "DJ add on N³");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
