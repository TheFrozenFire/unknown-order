\\ Additive shares and Shoup extract.  Mirrors ThresholdRSA.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 11; q = 17; N = p*q; e = 3; d = 27; lam = lcm(10,16);
m = 42;
d1 = 10; d2 = 17;
check(d1+d2 == d, "additive split of d");
s1 = lift(Mod(m,N)^d1); s2 = lift(Mod(m,N)^d2);
check(lift(Mod(s1,N)*Mod(s2,N)) == lift(Mod(m,N)^d), "m^{d1} m^{d2} = m^d");

\\ mediated / SEM: two parties
check(lift(Mod(m,N)^d1 * Mod(m,N)^d2) == lift(Mod(m,N)^d), "mediated RSA is two shares");

\\ Shoup: y = x^{k d}, k a = 1 + e t, y^a x^{-t} = x^d
x = 5; k = 4;
check(gcd(k,e)==1, "k coprime to e (Shoup 4Δ² shape)");
a = lift(1/Mod(k,e));
\\ k a = 1 + e t  with a in 0..e-1
t = (k*a - 1)/e;
check(k*a == 1 + e*t, "Bézout k a = 1 + e t");
y = lift(Mod(x,N)^(k*d));
xinv = lift(1/Mod(x,N));
comb = lift(Mod(y,N)^a * Mod(xinv,N)^t);
check(comb == lift(Mod(x,N)^d), "Shoup extract y^a x^{-t} = x^d");

\\ refresh: add z to one share, subtract from the other
z = 3;
check(lift(Mod(m,N)^(d1+z) * Mod(m,N)^(d2-z)) == lift(Mod(m,N)^d), "share refresh by zero");

\\ Shamir 2-of-3: f(X)=d+aX, 2 f(1) − f(2) = d, in the exponent
aa = 5;
s1 = lift(Mod(m,N)^(d+aa));
s2 = lift(Mod(m,N)^(d+2*aa));
s2inv = lift(1/Mod(s2,N));
check(lift(Mod(s1,N)^2 * Mod(s2inv,N)) == lift(Mod(m,N)^d), "2-of-3: s1² / s2 = m^d");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));

