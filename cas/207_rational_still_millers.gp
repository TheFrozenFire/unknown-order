\\ After reducing a rational invert-all-units map to y^d, Miller-from-d
\\ still splits.  Q coprime on units does not hide the trapdoor.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; N=pin_N;
g=gcd(2^10-1, N);
check(g==p,                             "Miller-from-d gcd is p");
check(1<g && g<N,                       "proper factor");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
