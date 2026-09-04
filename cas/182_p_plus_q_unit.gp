\\ Residue p is missing from the canonical F_q* samples used as
\\ units of N, but p+q is a unit of N with p+q ≡ p (mod q).  That
\\ lift fills the missing Fermat sample.  Mirrors SrsaRootPoly.v.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N;
y=p+q;
check(gcd(y,N)==1,                      "p+q is a unit of N");
check(y%q==p,                           "p+q ≡ p (mod q)");
check(y%p==q%p,                         "p+q ≡ q (mod p)");
check(gcd(p,q)==1,                      "p coprime to q so p is a unit of F_q");

y2=pin1363_p+pin1363_q;
check(gcd(y2,pin1363_N)==1,             "1363 p+q is a unit");
check(y2%pin1363_q==pin1363_p,          "1363 p+q ≡ p (mod q)");
y3=pin2491_p+pin2491_q;
check(gcd(y3,pin2491_N)==1,             "2491 p+q is a unit");
check(y3%pin2491_q==pin2491_p,          "2491 p+q ≡ p (mod q)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
