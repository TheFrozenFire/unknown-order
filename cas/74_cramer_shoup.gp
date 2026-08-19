\\ Cramer–Shoup 2000 verify is an e-th root.  Mirrors CramerShoup.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 11; q = 17; N = p*q; e = 3; d = 27;
x = 5; h = 6; m = 4;
y = lift(Mod(x * lift(Mod(h,N)^m), N)^d);
check(lift(Mod(y,N)^e) == (x * lift(Mod(h,N)^m)) % N, "y^e ≡ x h^m (mod N)");

\\ same e, two messages: (y/y')^e = h^{m-m'}
m2 = 1;
y2 = lift(Mod(x * lift(Mod(h,N)^m2), N)^d);
y2inv = lift(1/Mod(y2,N));
ratio = lift(Mod(y,N)*Mod(y2inv,N));
check(lift(Mod(ratio,N)^e) == lift(Mod(h,N)^(m-m2)), "(y/y')^e = h^{m-m'}");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
