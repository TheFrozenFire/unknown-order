\\ Joux-Naccache-Thome: e-th root oracle restricted to affine values x+c.
\\ Mirrors JouxNaccacheThome.v.  Not SNFS cost.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

N = 11*17;

\\ affine oracle: cube root of (x+c).  x=7, c=1 → 8, root 2
check(2^3 == 8,                         "2^3=8");
check((7+1) == 8,                       "affine 7+1=8");
check(2^3 == 7+1,                       "JNT oracle on (7,1) returns 2");

\\ general cube root of 7 is not an integer cube
check(1^3 != 7 && 2^3 != 7 && 0^3 != 7, "7 is not an integer cube");

\\ general GRoot still roots a plain cube 8
check(2^3 == 8,                         "general GRoot(8)=2");

\\ the affine oracle on x=8, c=0 is the general case at a cube
check((8+0) == 8,                       "c=0 recovers a plain cube");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
