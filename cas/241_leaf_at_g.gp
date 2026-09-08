\\ Residual leaf at generator g: dlog of x recovers d', Miller from
\\ e d' - 1.  Cube root of 3 is 3^27; 7th root is 3^23.
\\ Mirrors residual_leaf_at_g_extracts_and_factors.
\\ Not residual-solver => factor for every RSAInstance.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

oddpart(n) = { while(n%2==0, n = n/2); n };

N=pin_N; lam=pin_lam; g=pin_g; p=pin_p;

t3=lift(Mod(g,N)^pin_d);
k3=-1;
for(k=0, lam-1, if(lift(Mod(g,N)^k)==t3, k3=k));
check(k3==pin_d,                        "dlog_g of g^d recovers d");
check(lift(Mod(t3,N)^pin_e)==g,         "that power cubes to g");
check(gcd(lift(Mod(2,N)^(oddpart(pin_e*k3-1)*2))-1, N)==p, "Miller from 3*27-1 splits");

t7=lift(Mod(g,N)^23);
k7=-1;
for(k=0, lam-1, if(lift(Mod(g,N)^k)==t7, k7=k));
check(k7==23,                           "dlog_g of g^23 recovers 23");
check(lift(Mod(t7,N)^7)==g,             "that power is a 7th root of g");
check(gcd(lift(Mod(2,N)^(oddpart(7*k7-1)*2))-1, N)==p, "Miller from 7*23-1 splits");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
