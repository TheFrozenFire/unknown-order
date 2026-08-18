\\ Product of raw signatures.  Mirrors TranscriptOracle.v T7.
\\ rsa_test: 11·17, e=3, d=27.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 11; q = 17; N = p*q; d = 27;
check((3*d) % lcm(p-1,q-1) == 1, "d is the rsa_test inverse");

s1 = lift(Mod(2,N)^d); s2 = lift(Mod(3,N)^d); s3 = lift(Mod(5,N)^d);
sp = lift(Mod(2*3*5, N)^d);
check(sp == lift(Mod(s1,N)*Mod(s2,N)*Mod(s3,N)), "sign(2·3·5)=sign2·sign3·sign5");

\\ message product ≡ 1 ⇒ signature product ≡ 1
m1 = 4; m2 = 47;
check((m1*m2) % N == 1, "4·47 ≡ 1 (mod 187)");
check(lift(Mod(m1,N)^d * Mod(m2,N)^d) == 1, "sign(4)·sign(47) ≡ 1");

\\ weighted exponents commute with signing
a1 = 3; a2 = 2;
left = lift(Mod(lift(Mod(2,N)^a1)*lift(Mod(3,N)^a2), N)^d);
right = lift(Mod(s1,N)^a1 * Mod(s2,N)^a2);
check(left == right, "sign(2^3·3^2) = sign(2)^3·sign(3)^2");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
