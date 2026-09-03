\\ Cocks 2001 IBE algebra.  Mirrors Cocks.v.
\\ Blum/Williams N=11*23.  Carefully chosen a, decrypt Jacobi identity.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p = pin_253_p; q = pin_253_q; N = pin_253;

\\ pick a with Jacobi +1 that is a global square (the PKG-extractable one)
a = 3;
check(gcd(a,N)==1, "a unit");
check(kronecker(a,N)==1, "carefully chosen: Jacobi(a/N)=+1");
qr_a = (kronecker(a,p)==1 && kronecker(a,q)==1);
qr_na = (kronecker(-a,p)==1 && kronecker(-a,q)==1);
check(qr_a + qr_na == 1, "exactly one of {a,-a} is QR mod N");
check(qr_a, "this a is the global square");

\\ square root via CRT of p=3 mod 4 formula
sp = lift(Mod(a,p)^((p+1)/4));
sq = lift(Mod(a,q)^((q+1)/4));
s = lift(chinese(Mod(sp,p), Mod(sq,q)));
check((s*s) % N == a % N, "s^2 = a (PKG extracts the root)");

\\ encrypt a bit encoded as Jacobi(t/N)
t = 5;
check(gcd(t,N)==1, "t unit");
bit = kronecker(t, N);
tinv = lift(1/Mod(t,N));
c = (t + a*tinv) % N;
c2 = (c + 2*s) % N;
check(kronecker(c2, N) == bit, "Jacobi(c+2s) = Jacobi(t)  (decrypts the bit)");

\\ the other ciphertext, for -a, is what the encryptor also sends
check(kronecker(-a, N)==1, "(-a/N)=+1 too, so encryptor cannot tell");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
