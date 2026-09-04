\\ Any unit y ≡ p (mod q) fills the missing F_q* sample, not
\\ only p+q.  y = p + k q is a unit of N iff gcd(k, p)=1.
\\ Mirrors SrsaRootPoly.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N;
y2=p+2*q;
check(gcd(2,p)==1,                      "k=2 is coprime to p");
check(gcd(y2,N)==1,                     "p+2q is a unit of N");
check(y2%q==p,                          "p+2q ≡ p (mod q)");
y3=p+3*q;
check(gcd(3,p)==1,                      "k=3 is coprime to p");
check(gcd(y3,N)==1,                     "p+3q is a unit of N");
check(y3%q==p,                          "p+3q ≡ p (mod q)");
y11=p+p*q;
check(gcd(y11,N)==p,                    "p+p q shares p with N");

y1363=pin1363_p+2*pin1363_q;
check(gcd(y1363,pin1363_N)==1,          "1363 p+2q is a unit");
check(y1363%pin1363_q==pin1363_p,       "1363 p+2q ≡ p (mod q)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
