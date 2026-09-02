\\ Fifth hundred: leftover x is a Pohlig oracle; cubing 4-cycles;
\\ unit-group orders leak; two subgroups' cube roots split.
\\ Mirrors HundredX..AB.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p=11; q=17; N=p*q; lam=80; y=36; x=42;

\\ ----- X 401-420 Pohlig on leftover x, cubing 4-cycle -----
check(gcd(lift(Mod(x,N)^5)-1,N)==11,    "401 gcd(x^5-1,N)=11 Pohlig leftover x");
check(gcd(lift(Mod(x,N)^8)-1,N)==17,    "402 gcd(x^8-1,N)=17");
check(gcd(lift(Mod(x,N)^10)-1,N)==11,   "403 gcd(x^{10}-1,N)=11");
check(gcd(lift(Mod(x,N)^16)-1,N)==17,   "404 gcd(x^{16}-1,N)=17");
check(gcd(lift(Mod(x,N)^4)-1,N)==1,     "405 gcd(x^4-1,N)=1 no split at 4");
check(gcd(lift(Mod(x,N)^2)-1,N)==1,     "406 gcd(x^2-1,N)=1");
check(lift(Mod(x,N)^5)==111,            "407 x^5 ≡ 111 generates C8");
check(znorder(Mod(111,N))==8,           "407 ord(111)=8");
check(lift(Mod(x,N)^8)==69,             "408 x^8 ≡ 69 in C5");
check(znorder(Mod(69,N))==5,            "408 ord(69)=5");
check(lift(Mod(111,N)^5 * Mod(69,N)^2)==x, "409 111^5 * 69^2 ≡ 42 reconstructs x");
check(gcd(lift(Mod(y,N)^5)-1,N)==11,    "410 y and x are the same Pohlig oracle");
check(lift(Mod(70,N)^3)==x,             "411 70^3 ≡ 42 cubing 4-cycle");
check(lift(Mod(x,N)^3)==y,              "412 42^3 ≡ 36");
check(lift(Mod(y,N)^3)==93,             "413 36^3 ≡ 93");
check(lift(Mod(93,N)^3)==70,            "414 93^3 ≡ 70");
check(lift(Mod(3,40)^4)==1,             "415 3^4 ≡ 1 (mod 40) cubing order 4");
check(lift(Mod(27,40)^4)==1,            "416 27^4 ≡ 1 (mod 40)");
check(lift(Mod(9,N)^3)==168,            "417 9^3 ≡ 168 second 4-cycle");
check(lift(Mod(168,N)^3)==60,           "418 168^3 ≡ 60");
check(lift(Mod(15,N)^3)==9,             "419 15^3 ≡ 9 closes the cycle");
check(kronecker(x,N)==1 && kronecker(2,N)==-1, "420 Jacobi(x)=+1 Jacobi(2)=-1");

\\ ----- Y 421-440 unit-group orders -----
check(znorder(Mod(10,N))==16,           "421 10 has order 16");
check(lift(Mod(10,N)^8)==67,            "422 10^8 ≡ 67 Miller");
check(gcd(lift(Mod(10,N)^8)-1,N)==11,   "423 gcd(10^8-1,N)=11");
check(lift(Mod(10,N)^16)==1,            "424 10^{16} ≡ 1");
found=0; for(k=0,16, if(lift(Mod(10,N)^k)==x, found=1));
check(found==0,                         "425 42 not in <10>");
check(znorder(Mod(21,N))==4,            "426 21 has order 4");
check(lift(Mod(21,N)^2)==67,            "426 21^2 ≡ 67");
check(gcd(lift(Mod(21,N)^2)-1,N)==11,   "427 gcd(21^2-1,N)=11");
check(znorder(Mod(89,N))==4,            "428 89=y^{10} has order 4");
check(lift(Mod(120,N)^2)==1,            "429 120^2 ≡ 1 mixed sqrt");
check(gcd(120-1,N)==17,                 "429 gcd(120-1,N)=17");
check(gcd(120+1,N)==11,                 "429 gcd(120+1,N)=11");
check(lift(Mod(-1,N)^2)==1,             "430 (-1)^2 ≡ 1");
check(gcd(186-1,N)==1,                  "430 gcd(N-2,N)=1 no split");
check((p-1)==10 && (q-1)==16,           "431 p-1=10 q-1=16");
check(lcm(10,16)==lam,                  "432 λ=lcm(10,16)");
check((p-1)*(q-1)==160,                 "433 φ=10*16=160");
check(160/40==4,                        "434 [units : <y>] = 4");
check(znorder(Mod(x,N))==40,            "435 leftover x has order 40 not 16");
check(valuation(40,2)==3,               "436 v2(ord x)=3");
check(valuation(lam,2)==4,              "437 v2(λ)=4 > 3");
check(znorder(Mod(69,N))==5,            "438 69 generates the 5-Sylow C5");
check(znorder(Mod(111,N))==8,           "439 111 generates C8 = 2-primary of <y>");
check(znorder(Mod(x,N))%5==0,           "440 leftover x generates the 5-Sylow");

\\ ----- Z 441-460 pin 77, (Z/40Z)*, confinement -----
check(gcd(2^6-1,77)==7,                 "441 N=77: 2^6-1 splits 7");
check(gcd(2^10-1,77)==11,               "442 2^{10}-1 splits 11");
check(gcd(lift(Mod(51,77)^3)-1,77)==7,  "443 leftover 51^3-1 splits 7");
check(znorder(Mod(2,77))==30,           "444 ord(2)=λ=30 on 77");
check(27%8==3 && 27%5==2,               "445 k=27 ≡ (3,2) (mod 8,5)");
check(3%8==3 && 3%5==3,                 "446 e=3 ≡ (3,3) (mod 8,5)");
check(lift(Mod(3,40)^4)==1,             "447 (Z/40Z)* : 3 has order 4, not cyclic full");
check(kronecker(2,N)==-1,               "448 2 is Jacobi -1");
check(lift(Mod(2,N)^27)==161,           "449 2^{27} ≡ 161 cube root of 2");
check(lift(Mod(161,N)^3)==2,            "449 161^3 ≡ 2");
check(lift(Mod(3,N)^27)==75,            "450 3^{27} ≡ 75 SAGM of generator");
check(lift(Mod(75,N)^3)==3,             "450 75^3 ≡ 3");
check(75!=x,                            "451 75 is not the cube root of 36");
check(lift(Mod(y,N)^27)==x,             "452 36^{27} ≡ 42 trapdoor on this y");
check(kronecker(10,N)==1,               "453 10 is Jacobi +1 but order 16");
check(znorder(Mod(10,N))!=40,           "454 order-16 is not residual order");
check(kronecker(21,N)==-1,              "455 21 is Jacobi -1 order 4");
check(znorder(Mod(2,N))==40,            "456 <2> also has order 40");
check(lift(Mod(2,N)^1)!=y,              "457 <2> ≠ <y>");
check(gcd(161-x,N)==17,                 "458 gcd(2^{27}-36^{27},N)=17 two subgroups split");
check(160/40==4,                        "459 four cosets, residual x only in <y>");
check(lift(Mod(60,N)^3)==15,            "460 60^3 ≡ 15 third step of cycle 2");

\\ ----- AA 461-480 rest of cubing 4-cycles, four sqrt1 -----
check(lift(Mod(168,N)^3)==60,           "461 168^3 ≡ 60");
check(lift(Mod(25,N)^3)==104,           "462 25^3 ≡ 104 third 4-cycle");
check(lift(Mod(104,N)^3)==59,           "463 104^3 ≡ 59");
check(lift(Mod(59,N)^3)==53,            "464 59^3 ≡ 53");
check(lift(Mod(53,N)^3)==25,            "465 53^3 ≡ 25 closes cycle 3");
check(lift(Mod(49,N)^3)==26,            "466 49^3 ≡ 26 fourth 4-cycle");
check(lift(Mod(26,N)^3)==185,           "467 26^3 ≡ 185");
check(lift(Mod(185,N)^3)==179,          "468 185^3 ≡ 179");
check(lift(Mod(179,N)^3)==49,           "469 179^3 ≡ 49 closes cycle 4");
check(gcd(p-1,q-1)==2,                  "470 gcd(p-1,q-1)=2 matching orders only 1 or 2");
check(40%5==0,                          "471 5 | ord(y) so 5 | ord_p not ord_q");
check(40%8==0,                          "472 8 | ord(y) so 8 | ord_q not ord_p");
check(gcd(lift(Mod(3,N)^5)-1,N)==11,    "473 max-order 3 also Pohlig-splits at 5");
check(gcd(lift(Mod(3,N)^16)-1,N)==17,   "474 3^{16}-1 splits 17");
check(gcd(lift(Mod(3,N)^8)-1,N)==1,     "475 3^8-1 does not split");
check(121==11^2 && gcd(121,N)==11,      "476 120+1=121=p^2");
check(67-1==66 && gcd(66,N)==11,        "477 67-1=66 miller");
check(lift(Mod(1,N)^2)==1,              "478 four sqrt of 1: 1");
check(lift(Mod(186,N)^2)==1,            "478 -1");
check(lift(Mod(67,N)^2)==1,             "478 67");
check(lift(Mod(120,N)^2)==1,            "478 120");
check(lift(Mod(x,N)^16)==86,            "479 x^{16} ≡ 86 ≠ 1 so not order 16");
check(lift(Mod(x,N)^8)!=1,              "480 x^8 ≢ 1 not order 8");

\\ ----- AB 481-500 two instances one d, confinement -----
check(lift(Mod(2,N)^27)==161,           "481 cube root of 2 lives in <2>");
check(lift(Mod(3,N)^27)==75,            "482 cube root of 3 lives in <3>");
check(lift(Mod(y,N)^27)==42,            "483 cube root of 36 lives in <y>");
check(161!=42 && 75!=42,                "484 three different leftover x for one k=27");
check(gcd(161-42,N)==17,                "485 gcd of cube roots of 2 and 36 splits");
check(gcd(75-42,N)==11,                 "486 gcd(75-42,N)=11 cube roots of 3 and 36 split");
check(gcd(75-161,N)==1,                 "487 gcd(75-161,N)=1");
check(znorder(Mod(5,N))==80,            "488 5 has max order 80");
check(gcd(lift(Mod(5,N)^5)-1,N)==11,    "489 max-order 5 Pohlig at 5");
check(gcd(lift(Mod(5,N)^16)-1,N)==17,   "490 5^{16}-1 splits");
check(2^6 <= lam && lam < 2^7,          "491 λ in 7 bits");
check(valuation(lam,2)==4,              "491 2-Sylow height v2(λ)=4");
check(kronecker(x,N)==1,                "492 residual x is Jacobi +1");
check(kronecker(161,N)==kronecker(2,N), "493 cube root of 2 has Jacobi of 2");
check(lift(Mod(10,N)^8)==67,            "494 order-16 unit powers to Miller 67");
check(znorder(Mod(x,N))!=16,            "495 leftover x is not an order-16 unit");
check(znorder(Mod(x,N))!=10,            "496 leftover x is not order 10");
check(lift(Mod(51,77)^7)==lift(Mod(2,77)^{49}), "497 77: 51^7 = 2^{49}");
check(lcm(6,10)==30,                    "498 77 λ=30=2*3*5");
check(gcd(lift(Mod(2,77)^3)-1,77)==7,   "499 77: 2^3-1 splits 7 (ord_p=6 has 3)");
check(gcd(lift(Mod(2,77)^5)-1,77)==1,   "500 77: 2^5-1 does not split");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
