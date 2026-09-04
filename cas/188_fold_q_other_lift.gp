\\ An invert poly matches X^{d_q} at every lift of residue p,
\\ so fold_q(p) = p^{d_q} is independent of the lift.
\\ Mirrors SrsaRootPoly.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N;
da=pin_inv3_p; db=pin_inv3_q; ca=pin_root_ca; cb=pin_root_cb;
Pinv=ca*x^da + cb*x^db + N*x^20;

fold_at(aa) = {
  fv=0;
  for(r=0, q-2, cs=0; for(j=0, 8, cs += polcoeff(Pinv, r+j*(q-1))); fv += cs*aa^r);
  fv
};

want=lift(Mod(p,q)^db);
y1=p+q; y2=p+2*q; y3=p+3*q;
check(fold_at(y1)%q==want,              "fold_q(p+q) = p^{d_q}");
check(fold_at(y2)%q==want,              "fold_q(p+2q) = p^{d_q}");
check(fold_at(y3)%q==want,              "fold_q(p+3q) = p^{d_q}");
check(fold_at(p)%q==want,               "fold_q(p) = p^{d_q}");
check(lift((Mod(subst(Pinv,x,y2),N)^pin_e))==y2, "invert poly at p+2q");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
