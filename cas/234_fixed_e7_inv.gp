\\ Fixed residual e=7 with known inverse 23.  M = 7*23-1 = 160
\\ is a multiple of lam and Millers.  Not residual-solver => factor:
\\ Miller uses the inverse, not the solver.  Mirrors
\\ residual_solver_reduced_fixed_e_constructs_factor at e=7.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

oddpart(n) = { while(n%2==0, n = n/2); n };

N=pin_N; lam=pin_lam; p=pin_p; e=7; d=23;
M=e*d-1;
check((e*d)%lam==1,                     "7*23 cong 1 mod lam");
check(M==160,                           "M = 7*23-1 is 160");
check(M%lam==0,                         "lam divides M");
check(gcd(e,lam)==1,                    "gcd(7, lam)=1");
check(e%2==1,                           "7 is odd");
check((e-1)%lam!=0,                     "7 is a residual exponent");
check(gcd(lift(Mod(2,N)^(oddpart(M)*2))-1, N)==p, "Miller on M=160 splits");
check(lift(Mod(pin_y,N)^d)==60,         "pin y to 23 is 60");
check(lift(Mod(60,N)^e)==pin_y,         "60^7 is pin y");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
