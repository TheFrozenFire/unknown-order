\\ Residual solver returning e \equiv public e (mod lam) writes y^d.
\\ Non-minimal e = e+lam millers from (e-public e) without a new d.
\\ Trapdoor x at e+lam on every unit.  Not residual-solver => factor:
\\ unrestricted e may miss this congruence class.
\\ Mirrors residual_solver_reduced_e_cong_constructs_factor.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N=pin_N; e=pin_e; d=pin_d; lam=pin_lam; p=pin_p;
okx=1;
for(yy=1, N-1, \
  if(gcd(yy,N)==1, \
    xd=lift(Mod(yy,N)^d); \
    if(lift(Mod(xd,N)^(e+lam))!=yy, okx=0) \
  ) \
);
check(okx,                              "trapdoor x at e+lam on every unit");
check((e+lam-e)%lam==0,                 "e+lam cong e mod lam");
check(e+lam!=e,                         "e+lam is non-minimal");
check(gcd(lift(Mod(2,N)^10)-1, N)==p,   "Miller on recovered lam splits");
check(lift(Mod(pin_y,N)^d)==pin_x,      "trapdoor at pin y is leftover x");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
