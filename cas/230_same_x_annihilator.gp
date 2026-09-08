\\ Same x at two residual exponents annihilates x^{e'-e}.
\\ e'-e = lam is two-sided: gcd(x^lam-1, N)=N, not a proper factor.
\\ e'-e = 4 (public 3 vs 7) does not miller.  Leftover k=5 does split.
\\ Mirrors same_unit_x_two_exponents_annihilates / powm_one_gcd_is_N.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N=pin_N; x=pin_x; lam=pin_lam;
check(lift(Mod(x,N)^lam)==1,            "x^lam is 1");
check(gcd(lift(Mod(x,N)^lam)-1, N)==N,  "gcd(x^lam-1, N)=N (two-sided)");
check(gcd(lift(Mod(x,N)^(2*lam))-1, N)==N, "gcd(x^{2 lam}-1, N)=N");
check(gcd(lift(Mod(x,N)^4)-1, N)==1,    "gcd(x^4-1, N)=1 (7-3 does not miller)");
check(gcd(lift(Mod(x,N)^pin_x_k)-1, N)==pin_p, "leftover k=5 one-sided splits");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
