\\ Other fixed residual e with known inverse: e=11 (inv 51), e=79
\\ (inv 79), e=9 (inv 9).  Each M = e*d-1 is a lam-multiple and
\\ Millers.  Not residual-solver => factor: Miller uses the inverse.
\\ Mirrors residual_solver_reduced_fixed_e_constructs_factor.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

oddpart(n) = { while(n%2==0, n = n/2); n };

N=pin_N; lam=pin_lam; p=pin_p; y=pin_y;

e=11; d=51; M=e*d-1;
check((e*d)%lam==1,                     "11*51 cong 1 mod lam");
check(M%lam==0,                         "lam divides 11*51-1");
check(gcd(lift(Mod(2,N)^(oddpart(M)*2))-1, N)==p, "Miller on M=11*51-1 splits");
check(lift(Mod(y,N)^d)==25,             "pin y to 51 is 25");
check(lift(Mod(25,N)^e)==y,             "25^11 is pin y");

e=79; d=79; M=e*d-1;
check((e*d)%lam==1,                     "79*79 cong 1 mod lam");
check(M%lam==0,                         "lam divides 79*79-1");
check(gcd(lift(Mod(2,N)^(oddpart(M)*2))-1, N)==p, "Miller on M=79*79-1 splits");
check(lift(Mod(y,N)^d)==26,             "pin y to 79 is 26");
check(lift(Mod(26,N)^e)==y,             "26^79 is pin y");

e=9; d=9; M=e*d-1;
check((e*d)%lam==1,                     "9*9 cong 1 mod lam");
check(M==lam,                           "9*9-1 is lam");
check(gcd(lift(Mod(2,N)^(oddpart(M)*2))-1, N)==p, "Miller on M=80 splits");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
