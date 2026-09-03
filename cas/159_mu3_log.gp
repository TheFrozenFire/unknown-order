\\ Local discrete log on mu_3 is additive: log(xy) ≡ log x + log y (mod 3).
\\ Reconstruction: x ≡ omega^{log_omega(x)}.  Either generator (omega or
\\ omega^2) still adds.  This is the identity that makes mu3N_det bilinear
\\ (CAS 158 enumerates bilinear; this file pins the log).  Named extra
\\ 13×7=91; pin kernel {1} so log is constantly 0.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p = pin_91_p; q = pin_91_q; N = pin_91;
om_p = pin_91_om_p; om_q = pin_91_om_q;

mu3_log(om, x, m) = if((x % m) == lift(Mod(om, m)^0), 0, if((x % m) == lift(Mod(om, m)^1), 1, 2));

w13 = [1, 3, 9];
w7 = [1, 2, 4];

recon_ok(om, L, m) = {
  okc = 1;
  for(i = 1, #L, if(lift(Mod(om, m)^mu3_log(om, L[i], m)) != L[i] % m, okc = 0));
  okc
};
check(recon_ok(om_p, w13, p),            "reconstruct F_13*: x ≡ 3^{log x}");
check(recon_ok(om_q, w7, q),             "reconstruct F_7*: x ≡ 2^{log x}");
check(recon_ok(9, w13, p),               "reconstruct F_13* wrt omega^2=9");
check(recon_ok(4, w7, q),                "reconstruct F_7* wrt omega^2=4");

add_ok(om, L, m) = {
  okc = 1;
  for(i = 1, #L, for(j = 1, #L, if(mu3_log(om, lift(Mod(L[i]*L[j], m)), m) != (mu3_log(om, L[i], m) + mu3_log(om, L[j], m)) % 3, okc = 0)));
  okc
};
check(add_ok(om_p, w13, p),              "log additive on mu_3(F_13*)");
check(add_ok(om_q, w7, q),               "log additive on mu_3(F_7*)");
check(add_ok(9, w13, p),                 "log wrt omega^2 still additive on F_13*");
check(add_ok(4, w7, q),                  "log wrt omega^2 still additive on F_7*");

check(lift(Mod(om_p, p)^0) != lift(Mod(om_p, p)^1), "1 ≠ omega on F_13*");
check(lift(Mod(om_p, p)^0) != lift(Mod(om_p, p)^2), "1 ≠ omega^2 on F_13*");
check(lift(Mod(om_p, p)^1) != lift(Mod(om_p, p)^2), "omega ≠ omega^2 on F_13*");
check(znorder(Mod(om_p, p)) == 3,        "ord(3)=3 in F_13*");
check(znorder(Mod(om_q, q)) == 3,        "ord(2)=3 in F_7*");

exp_p(x) = mu3_log(om_p, x, p);
exp_q(x) = mu3_log(om_q, x, q);
det(x, y) = lift(Mod(om_p, p)^((exp_p(x)*exp_q(y) - exp_q(x)*exp_p(y)) % 3));

ker_of(m) = {
  L = List();
  for(x = 1, m-1, if(gcd(x,m)==1 && lift(Mod(x,m)^3)==1, listput(L, x)));
  L
};
ker = ker_of(N);
check(#ker == 9,                          "9 kernel elements on 91");

left_bil(L) = {
  okc = 1;
  for(i = 1, #L, for(j = 1, #L, for(k = 1, #L, if(det(lift(Mod(L[i]*L[j], N)), L[k]) != lift(Mod(det(L[i],L[k])*det(L[j],L[k]), p)), okc = 0))));
  okc
};
right_bil(L) = {
  okc = 1;
  for(i = 1, #L, for(j = 1, #L, for(k = 1, #L, if(det(L[i], lift(Mod(L[j]*L[k], N))) != lift(Mod(det(L[i],L[j])*det(L[i],L[k]), p)), okc = 0))));
  okc
};
check(left_bil(ker),                      "left bilinear via logs on 9-kernel");
check(right_bil(ker),                     "right bilinear via logs on 9-kernel");

skew_ok(L) = {
  okc = 1;
  for(i = 1, #L, for(j = 1, #L, if(det(L[j], L[i]) != lift(Mod(det(L[i], L[j]), p)^2), okc = 0)));
  okc
};
check(skew_ok(ker),                       "e(y,x) = e(x,y)^2 (skew, order 3)");

Npin = pin_N;
check(#ker_of(Npin) == 1,                 "pin kernel {1}");
check(mu3_log(2, 1, 11) == 0,             "pin log of 1 is 0");
check(add_ok(2, [1], 11),                 "pin log additive on {1}");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
