\\ Residual e+k*lam keeps the same x.  Pin: (42, 83) for y=36.
\\ Shape: still odd, gcd(e+lam, lam)=gcd(e, lam), lam ndiv (e+lam-1).
\\ Mirrors residual_leaf_plus_k_lam / residual_shaped_e_plus_k_lam.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N=pin_N; e=pin_e; lam=pin_lam; x=pin_x; y=pin_y;
ep=e+lam;
check(lift(Mod(x,N)^ep)==y,             "x^{e+lam} is y");
check(lift(Mod(x,N)^e)==y,              "x^e is y (same x)");
check(ep%2==1,                          "e+lam is odd");
check(gcd(ep, lam)==gcd(e, lam),        "gcd(e+lam, lam)=gcd(e, lam)");
check(gcd(ep, lam)==1,                  "gcd(e+lam, lam)=1");
check((ep-1)%lam==(e-1)%lam,            "lam | (e+lam-1) iff lam | (e-1)");
check((ep-1)%lam!=0,                    "e+lam is a residual exponent");
check(ep==83,                           "pin e+lam is 83");
check(lift(Mod(x,N)^(e+2*lam))==y,      "x^{e+2 lam} is y");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
