\\ Conjunction of residual, not-a-factor, peel, and all 100 class fates
\\ on the default pin (N,y,x,e)=(187,36,42,3).  Loads cas/lib/{pin,classes}.gp.
\\ This is an AND of recorded fates, not an OR of solvers, and not a
\\ proof that the residual cube factors.  Numbered files 01-133 stay.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");
read("lib/classes.gp");

init_pin();
check(N==pin_N && y==pin_y && x==pin_x && e==pin_e && lam==pin_lam, "default pin");
check(Pin==[pin_N, pin_y, pin_x, pin_e, pin_lam], "Pin vector");

check(residual(),                        "residual cube 42^3 == 36");
check(!factor_from_x(),                  "x is not a factor of N");
check(peel_nonunit(),                    "peel non-unit x");
check(peel_units(),                      "peel unit cube");
check(peel_jacobi(),                     "peel Jacobi");
check(peel_even(),                       "peel even e");
check(peel_mixed(),                      "peel mixed square root");
check(peel_miller(),                     "peel Miller on lambda-type");
check(peel_all(),                        "peel conjunction");

C = class_vec();
check(#C==100,                           "class_vec has 100 predicates");
for(i=1,#C, \
  check(C[i](), Str("cl ", if(i<10,"0",""), i)) \
);
check(classes_all(),                     "classes 01-100 conjunction");
check(whole(),                           "whole identity on the default pin");

\\ Named extra pins: in-corpus second moduli, not a replacement of 187.
check(extra_77()==[pin_77, pin_77_y, pin_77_x, pin_77_e, pin_77_lam], "extra pin 77 vector");
check(extra_77_residual(),               "extra pin 77 residual 2^7 == 51");
check(extra_253_ok(),                    "extra pin 253 Williams pair");
check(extra_45_ok(),                     "extra pin 45 Takagi / OU");
check(extra_105_ok(),                    "extra pin 105 triprime");
check(extra_247_ok(),                    "extra pin 247 coprime modulus");
check(extra_Nsq_ok(),                    "extra pin N^2 Paillier carrier");

\\ Extra moduli are different sentences: they are not the default Pin.
check(extra_77()[1]!=N,                  "77 is not the default N");
check(extra_253()[1]!=N,                 "253 is not the default N");
check(extra_45()[1]!=N,                  "45 is not the default N");
check(extra_105()[1]!=N,                 "105 is not the default N");
check(extra_247()[1]!=N,                 "247 is not the default N");
check(extra_Nsq()[1]!=N,                 "N^2 is not the default N");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
