\\ Garner CRT decrypt equals c^d.  Mirrors CRTRSA.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 11; q = 17; N = p*q; e = 3; d = 27;
c = 36;
dp = d % (p-1); dq = d % (q-1);
mp = lift(Mod(c,p)^dp); mq = lift(Mod(c,q)^dq);
x = lift(chinese([Mod(mp,p), Mod(mq,q)]));
check(x % N == lift(Mod(c,N)^d), "CRT decrypt = c^d");
check(lift(Mod(c,N)^d) == 42, "rsa_test: dec(36)=42");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
