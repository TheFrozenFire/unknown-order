\\ CAS — (2/p) supplementary law and Euler ±1.  Mirrors QuadRecip.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

check(11 % 8 == 3 && kronecker(2,11) == -1, "11≡3 (mod 8): (2/11)=−1");
check(23 % 8 == 7 && kronecker(2,23) == 1,  "23≡7 (mod 8): (2/23)=+1");
check(17 % 8 == 1 && kronecker(2,17) == 1,  "17≡1 (mod 8): (2/17)=+1");
check(13 % 8 == 5 && kronecker(2,13) == -1, "13≡5 (mod 8): (2/13)=−1");

check(lift(Mod(2,11)^5) == 10,              "2^{(11−1)/2} ≡ −1 (mod 11)");
check(lift(Mod(2,23)^11) == 1,              "2^{(23−1)/2} ≡ +1 (mod 23)");
check(kronecker(-1,11) == -1,               "(−1/11)=−1 (11≡3 mod 4)");
check(kronecker(-1,13) == 1,                "(−1/13)=+1 (13≡1 mod 4)");

\\ 4 is a square, Euler +1; 2 is QNR mod 11, Euler −1
check(lift(Mod(4,11)^5) == 1,               "QR 4 has Euler value +1");
check(!issquare(Mod(2,11)),                 "2 is QNR mod 11");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
