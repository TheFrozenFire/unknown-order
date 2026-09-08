\\ Discrete log of the solver's x at generator g recovers d'.
\\ Trapdoor at e=3: 3^27; at e=7: 3^23.  Search k < lam.
\\ Mirrors pin_dlog_mod_lam / residual_solver_fixed_e_extracts_d.
\\ Miller uses the recovered k, not a handed inverse.
\\ Not residual-solver => factor: e is still fixed.
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
check(lift(Mod(t3,N)^pin_e)==g,         "that power is a cube root of g");

t7=lift(Mod(g,N)^23);
k7=-1;
for(k=0, lam-1, if(lift(Mod(g,N)^k)==t7, k7=k));
check(k7==23,                           "dlog_g of g^23 recovers 23");
check(lift(Mod(t7,N)^7)==g,             "that power is a 7th root of g");
check(gcd(lift(Mod(2,N)^(oddpart(7*k7-1)*2))-1, N)==p, "Miller from recovered 23 splits");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
