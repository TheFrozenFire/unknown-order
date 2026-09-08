\\ Residual e=7 is not 3 (mod lam).  Unique unit 7th root of 36 is 60,
\\ not leftover 42.  7^{-1} \equiv 23 (mod lam).  gcd(60^4-1, N)=1.
\\ Mirrors pin_e7_residual / pin_e7_x_neq_pin_x.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N=pin_N; lam=pin_lam; y=pin_y;
inv7=lift(1/Mod(7,lam));
x7=lift(Mod(y,N)^inv7);
check(inv7==23,                         "7 inverse mod lam is 23");
check(x7==60,                           "y^23 is 60");
check(lift(Mod(x7,N)^7)==y,             "60^7 is 36");
check(x7!=pin_x,                        "7th root is not leftover x");
check(gcd(7,lam)==1,                    "gcd(7, lam)=1");
check(7%2==1,                           "7 is odd");
check((7-1)%lam!=0,                     "7 is a residual exponent");
check(gcd(lift(Mod(x7,N)^4)-1, N)==1,   "gcd(60^4-1, N)=1");
check((7-pin_e)%lam!=0,                 "7 not cong public e mod lam");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
