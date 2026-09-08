\\ Strong-RSA solver with lam | e-1: Miller-from-(e-1).
\\ lambda+1=81, e-1=80 millers.  Residual e=3, e-1=2 does not.
\\ e=241 = 3*lam+1 millers from 240.  Residual forbids the class.
\\ Mirrors strong_rsa_solver_annihilator_e_constructs_factor.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

oddpart(n) = { while(n%2==0, n = n/2); n };

N=pin_N; lam=pin_lam; p=pin_p;

check((81-1)%lam==0,                    "lam divides 81-1");
check(gcd(lift(Mod(2,N)^(oddpart(80)*2))-1, N)==p, "Miller from 80 splits");
check((3-1)%lam!=0,                     "lam does not divide 3-1");
check(gcd(3, N)==1,                     "Miller from 2 does not split");
check((241-1)%lam==0,                   "lam divides 241-1");
check(gcd(lift(Mod(2,N)^(oddpart(240)*2))-1, N)==p, "Miller from 240 splits");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
