\\ DARK degree-1 and degree-2 exponent identities.  Mirrors Dark.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

N = 11*17;
g = 3;
s = 9; z = 4;
a0 = 2; a1 = 5; a2 = 3;

f1(x) = a0 + a1*x;
q1 = a1;
check(f1(s) - f1(z) == q1*(s - z), "deg1: f(s)-f(z) = q (s-z)");
C1 = lift(Mod(g, N)^f1(s));
pi1 = lift(Mod(g, N)^q1);
rhs1 = (lift(Mod(pi1, N)^(s-z)) * lift(Mod(g, N)^f1(z))) % N;
check(C1 == rhs1, "deg1: C = pi^{s-z} * g^{f(z)}");

f2(x) = a0 + a1*x + a2*x*x;
q2 = a1 + a2*(s + z);
check(f2(s) - f2(z) == q2*(s - z), "deg2: f(s)-f(z) = q(s)(s-z)");
C2 = lift(Mod(g, N)^f2(s));
pi2 = lift(Mod(g, N)^q2);
rhs2 = (lift(Mod(pi2, N)^(s-z)) * lift(Mod(g, N)^f2(z))) % N;
check(C2 == rhs2, "deg2: C = pi^{s-z} * g^{f(z)}");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
