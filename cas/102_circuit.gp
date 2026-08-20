\\ Two-gate circuit z = x*y + t.  Mirrors Circuit.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

N = 11*17; g = 3; tau = 5;
x = 3; y = 4; t = 2; z = 14;
m = x*y;
check(z == m + t, "circuit sat");
check(m == 12, "mul wire");
check(lift(Mod(g,N)^(m)) * lift(Mod(g,N)^t) % N == lift(Mod(g,N)^z), \
  "add encodings");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
