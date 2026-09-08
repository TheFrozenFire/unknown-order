\\ Inverse of residual e mod lam is Bézout, not an extra hyp.
\\ gcdext(7,80)=(23,-2), gcdext(3,80)=(27,-1),
\\ gcdext(11,80)=(-29,4) and -29 cong 51 mod 80.
\\ Mirrors residual_inv_mod_lam.  Miller uses (e, lam).
\\ Not residual-solver => factor.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

lam=pin_lam;

b7=gcdext(7,lam);
check(b7[1]*7 + b7[2]*lam==1,           "Bezout 7*u + lam*v = 1");
check((b7[1] % lam)==23,                "7 inverse is 23");
check((7*23)%lam==1,                    "7*23 cong 1 mod lam");

b3=gcdext(3,lam);
check(b3[1]*3 + b3[2]*lam==1,           "Bezout 3*u + lam*v = 1");
check((b3[1] % lam)==27,                "3 inverse is pin_d");
check((3*27)%lam==1,                    "3*27 cong 1 mod lam");

b11=gcdext(11,lam);
check(b11[1]*11 + b11[2]*lam==1,        "Bezout 11*u + lam*v = 1");
check(((b11[1] % lam)+lam)%lam==51,     "11 inverse is 51");
check((11*51)%lam==1,                   "11*51 cong 1 mod lam");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
