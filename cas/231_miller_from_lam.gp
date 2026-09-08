\\ Miller from a known multiple of lam splits.  M = lam, 2*lam, 3*lam,
\\ and recovered e+lam-e all give p.  On this pin ed-1 = lam, so
\\ Miller-from-d is Miller-from-lam.  Writing M wrote lam.
\\ Not residual-solver => factor.  Mirrors pin_miller_from_lambda_multiple.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

oddpart(n) = { while(n%2==0, n = n/2); n };
val2(n) = valuation(n, 2);

N=pin_N; p=pin_p; lam=pin_lam;
check((pin_e*pin_d-1)==lam,             "ed-1 = lam on this pin");
check(oddpart(lam)==5,                  "odd_part(lam)=5");
check(gcd(lift(Mod(2,N)^(oddpart(lam)*2))-1, N)==p, "Miller on M=lam splits");
check(oddpart(2*lam)==5,                "odd_part(2 lam)=5");
check(gcd(lift(Mod(2,N)^(oddpart(2*lam)*2))-1, N)==p, "Miller on M=2 lam splits");
check(oddpart(3*lam)==15,               "odd_part(3 lam)=15");
check(gcd(lift(Mod(2,N)^(oddpart(3*lam)*2))-1, N)==p, "Miller on M=3 lam splits");
Mrec=(pin_e+lam)-pin_e;
check(Mrec==lam,                        "recovered (e+lam)-e is lam");
check(gcd(lift(Mod(2,N)^(oddpart(Mrec)*2))-1, N)==p, "Miller on recovered (e+lam)-e splits");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
