\\ Frozen pins vs campaign alias.  pin_* is a retargetable alias;
\\ pin187_* / pin1363_* / pin2491_* are never rewritten by swap.
\\ Accident residues live on pin187.  Probe names avoid "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

check(pin_p==pin187_p,                  "campaign pin_p aliases pin187_p");
check(pin_q==pin187_q,                  "campaign pin_q aliases pin187_q");
check(pin_N==pin187_N,                  "campaign pin_N aliases pin187_N");
check(pin_y==pin187_y,                  "campaign pin_y aliases pin187_y");
check(pin_x==pin187_x,                  "campaign pin_x aliases pin187_x");
check(pin_e==pin187_e,                  "campaign pin_e aliases pin187_e");
check(pin_d==pin187_d,                  "campaign pin_d aliases pin187_d");
check(pin_lam==pin187_lam,              "campaign pin_lam aliases pin187_lam");

check(pin187_p==11 && pin187_q==17,     "pin187 is 11×17");
check(pin187_N==187,                    "pin187_N=187");
check(lift(Mod(pin187_x, pin187_N)^pin187_e)==pin187_y, "pin187 leftover cube");
check(lift(Mod(pin187_y, pin187_N)^pin187_d)==pin187_x, "pin187 y^d is leftover x");
check(gcd(pin187_e, pin187_lam)==1,     "pin187 e coprime to λ");

check(pin1363_p==29 && pin1363_q==47,   "pin1363 is 29×47");
check(pin1363_N==1363,                  "pin1363_N=1363");
check(gcd(3, pin1363_lam)==1,           "pin1363 admits e=3");
check(lift(Mod(pin1363_x, pin1363_N)^pin1363_e)==pin1363_y, "pin1363 leftover cube");

check(pin2491_p==47 && pin2491_q==53,   "pin2491 is 47×53");
check(pin2491_N==2491,                  "pin2491_N=2491");
check(gcd(3, pin2491_lam)==1,           "pin2491 admits e=3");
check(lift(Mod(pin2491_x, pin2491_N)^pin2491_e)==pin2491_y, "pin2491 leftover cube");

check(pin_N!=pin1363_N,                 "campaign is not the 1363 test pin");
check(pin_N!=pin2491_N,                 "campaign is not the 2491 test pin");

\\ 187-only cubing orbit, named on the frozen pin
check(lift(Mod(pin187_y, pin187_N)^pin187_e)==93, "pin187 y^e = 93");
check(lift(Mod(93, pin187_N)^pin187_e)==70, "pin187 93^e = 70");
check(lift(Mod(70, pin187_N)^pin187_e)==pin187_x, "pin187 70^e = leftover x");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
