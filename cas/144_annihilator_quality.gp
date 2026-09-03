\\ Annihilator quality short of λ: a scale of M with gcd(y^M-1,N).
\\ M=2,4 no split; odd part 5 and 2-power 8/16 split; ord=40 inverts
\\ with gcd=N; λ=80 annihilates and Miller 67 splits.
\\ Mirrors SrsaPeriod.v / SolverShape.v.  Residual leaf named, not solved.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; lam=pin_lam; y=pin_y;

check(lam == 16*5,                      "λ=16·5: v2=4, odd part 5");
check(16 == 2^4,                        "2-primary of λ is 16");
check(gcd(lift(Mod(y,N)^2)-1, N) == 1,  "M=2 (e=3 minus 1): no split");
check(gcd(lift(Mod(y,N)^4)-1, N) == 1,  "M=4: no split");
check(gcd(lift(Mod(y,N)^5)-1, N) == 11, "odd-part advice M=5: splits");
check(gcd(lift(Mod(y,N)^8)-1, N) == 17, "v2-advice M=8: splits");
check(gcd(lift(Mod(y,N)^16)-1, N) == 17,"v2-advice M=16=2^{v2(λ)}: splits");
check(lift(Mod(y,N)^40) == 1,           "M=ord(y)=40: annihilates y");
check(gcd(lift(Mod(y,N)^40)-1, N) == N, "M=40: gcd=N, leftover invert, no proper factor");
check(lift(Mod(y,N)^80) == 1,           "M=λ=80: annihilates y");
check(gcd(67-1, N) == 11,               "M=λ still Miller-splits on 67");
check(gcd(lift(Mod(y,N)^10)-1, N) == 11,"e=11 miller M=e-1=10: splits");
check(znorder(Mod(y,N)) == 40,          "ord(y)=40 is the invert-without-split rung");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
