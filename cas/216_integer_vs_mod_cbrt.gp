\\ p is not a Z-cube: integer cube-root misses (returns the handle).
\\ Modular cube-root of p is 165.  Mirrors SrsaModCbrt.v.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p;
check(ispower(p, 3)==0,                 "p is not a Z-cube");
check(2^3!=p && 3^3!=p,                 "nearby integer cubes miss p");
check(165!=p,                           "modular cube-root 165 is not p");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
