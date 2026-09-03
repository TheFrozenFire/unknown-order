\\ φ = λ · gcd(p−1, q−1) on a semiprime.  Mirrors PhiLambda.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p = pin_p; q = pin_q;
phi = (p-1)*(q-1); lam = lcm(p-1, q-1); g = gcd(p-1, q-1);
check(phi == 160 && lam == 80 && g == 2, "11·17: φ=160, λ=80, gcd=2");
check(phi == lam * g, "φ = λ · gcd");
check(phi / lam == g, "φ/λ = gcd");

p = 11; q = 13;
phi = (p-1)*(q-1); lam = lcm(p-1, q-1); g = gcd(p-1, q-1);
check(phi == 120 && lam == 60 && g == 2, "11·13: φ=120, λ=60, gcd=2");
check(phi == lam * g, "φ = λ · gcd (second pair)");

\\ not always 2: 7 and 13 give gcd(6,12)=6
p = 7; q = 13;
phi = (p-1)*(q-1); lam = lcm(p-1, q-1); g = gcd(p-1, q-1);
check(g == 6 && lam == 12 && phi == 72, "7·13: gcd=6, λ=12, φ=72");
check(phi == lam * g, "φ = λ · gcd when gcd > 2");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
