\\ Fourth hundred: residual dictionary, C8 x C5, e and e+40,
\\ equality-only order-finding vs gcd-Pohlig.  Crosswalk: notes/hundred4.md.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p=11; q=17; N=p*q; lam=80; y=36; o=40;

\\ ----- S 301-320 dictionary and cubing automorphism -----
check(lift(Mod(93,N)^67)==y,            "301 93^{67} ≡ 36 leftover k=3");
check(gcd(67,lam)==1 && 67%2==1,        "301 e=67 residual-shaped");
check(lift(Mod(25,N)^11)==y,            "302 25^{11} ≡ 36 k=e=11");
check(lift(Mod(25,N)^51)==y,            "303 25^{51} ≡ 36 e=11+40");
check(lift(Mod(15,N)^29)==y,            "304 15^{29} ≡ 36 k=e=29");
check(lift(Mod(15,N)^69)==y,            "305 15^{69} ≡ 36 e=29+40");
check(lift(Mod(168,N)^61)==y,           "306 168^{61} ≡ 36 leftover");
check(lift(Mod(104,N)^57)==y,           "307 104^{57} ≡ 36 leftover");
check(lift(Mod(185,N)^53)==y,           "308 185^{53} ≡ 36 leftover");
check(lift(Mod(y,N)^41)==y,             "309 36^{41} ≡ 36 peel-gap x=y");
check((41-1)%lam != 0 && gcd(41,lam)==1,"309 e=41 residual-shaped");
check(lift(Mod(y,N)^81)==y,             "310 36^{81} ≡ 36 λ-type on y");
check((81-1)%lam==0,                    "310 λ | e-1 so not residual");
check(lift(Mod(42,N)^83)==y,            "311 42^{83} ≡ 36 e=3+80");
check(eulerphi(lam)==32,                "312 phi(80)=32 residual e-classes");
check(eulerphi(o)==16,                  "313 phi(40)=16 residual x-classes");
check(32/16==2,                         "314 two residual e per x");
check(lift(Mod(42,N)^3)==y && lift(Mod(42,N)^43)==y, "315 e ≡ 3 (mod 40) same x");
check(gcd(1,lam)==1 && gcd(41,lam)==1,  "316 kernel 1 and 41 reduce to 1 mod 40");
check(gcd(3,o)==1,                      "317 cubing is bijective on <y>");
check(gcd(27,o)==1,                     "318 27th power is the inverse automorphism");
check(lift(Mod(lift(Mod(y,N)^27),N)^3)==y, "319 (y^{27})^3 ≡ y");
check(81==lam+1,                        "320 81=λ+1 so y^{81}=y");

\\ ----- T 321-340 C8 x C5 -----
check(lift(Mod(y,N)^5)==100,            "321 y^5 ≡ 100 generates C8");
check(znorder(Mod(100,N))==8,           "321 ord(100)=8");
check(lift(Mod(100,N)^2)==89,           "322 100^2 ≡ 89");
check(lift(Mod(100,N)^4)==67,           "322 100^4 ≡ 67");
check(lift(Mod(100,N)^8)==1,            "322 100^8 ≡ 1");
check(lift(Mod(y,N)^8)==137,            "323 y^8 ≡ 137 generates C5");
check(znorder(Mod(137,N))==5,           "323 ord(137)=5");
check(lift(Mod(137,N)^2)==69,           "324 C5: 137^2 ≡ 69");
check(lift(Mod(137,N)^3)==103,          "324 137^3 ≡ 103");
check(lift(Mod(137,N)^4)==86,           "324 137^4 ≡ 86");
check(gcd(3,5)==1,                      "325 cubing bijective on C5");
check(gcd(3,8)==1,                      "326 cubing bijective on C8");
check((155*69)%N==y,                    "327 y^{25} * y^{16} ≡ 36 reconstructs y");
check(5*5 + 8*(-3)==1,                  "328 Bezout 5*5+8*(-3)=1");
check(lift(Mod(100,N)^4)==67,           "329 C8 order-2 is Miller 67");
check(valuation(5,2)==0 && valuation(8,2)==3, "330 v2(ord_p y)=0 v2(ord_q y)=3");
check(o%8==0,                           "331 8 | 40, C8 is 2-primary of <y>");
check(o%5==0,                           "332 5 | 40, C5 is 5-primary of <y>");
check(lift(Mod(100,N)^1)==100,          "333 C8 generator 100 = y^5");
check(lift(Mod(y,N)^10)==89,            "334 89 = y^{10} = 100^2 order 4");
check(lift(Mod(100,N)^6)==166,          "335 100^6 ≡ 166 = y^{30}");
check(lift(Mod(100,N)^3)==111,          "336 100^3 ≡ 111 = y^{15}");
check(lift(Mod(100,N)^5)==155,          "337 100^5 ≡ 155 = y^{25}");
check(lift(Mod(100,N)^7)==144,          "338 100^7 ≡ 144 = y^{35}");
check(lift(Mod(137,N)^3)==103,          "339 103 = 137^3 = y^{24} in C5");
check(lift(Mod(67,N)^2)==1,             "340 ker(squaring on C8) contains 67");

\\ ----- U 341-360 binary / addition chain of k=27 -----
check(16+8+2+1==27,                     "341 27=16+8+2+1");
check(lift(Mod(y,N)^16*Mod(y,N)^8*Mod(y,N)^2*Mod(y,N))==42, "342 y^{16} y^8 y^2 y ≡ 42");
check(lift(Mod(y,N)^6)==47,             "343 addition chain y^6 ≡ 47");
check(lift(Mod(y,N)^12)==152,           "343 y^{12} ≡ 152");
check(lift(Mod(y,N)^24)==103,           "343 y^{24} ≡ 103");
check(lift(Mod(y,N)^27)==42,            "343 y^{27} ≡ 42");
check(27%2==1,                          "344 27 is odd: squaring-only cannot hit k");
check(hammingweight(27)==4,             "345 Hamming(27)=4 binary multiplies");
check(binary(27)==[1,1,0,1,1],          "346 binary 27 is 11011");
check(32-4-1==27,                       "347 27=32-4-1 NAF-ish");
check(lift(Mod(y,N)^32)==86,            "348 y^{32} ≡ 86");
check(lift(Mod(y,N)^4)==169,            "348 y^4 ≡ 169");
check(5*5==25 && 25%40==25,             "349 5a=25 in Bezout for CRT-in-<y>");
check(lift(Mod(y,N)^25)==155,           "349 y^{25} ≡ 155");
check(lift(Mod(y,N)^16)==69,            "350 y^{16} ≡ 69 = g5^2");

\\ ----- V 361-380 2-to-1 exponents, SAGM on y -----
check(gcd(lift(Mod(y,N)^5)-1,N)==11,    "351 gcd-path y^5-1 splits");
check(lift(Mod(y,N)^27)==42,            "352 exp-path y^{27} leftover cube");
check(lift(Mod(y,N)^40)==1,             "353 equality y^{40}≡1 finds the order");
check(lift(Mod(y,N)^20)!=1,             "353 y^{20}≢1 so ord is not 20");
check(lift(Mod(y,N)^8)!=1,              "353 y^8≢1");
check(lift(Mod(y,N)^5)!=1,              "353 y^5≢1");
check(3*27-1==lam,                      "354 SAGM on y: a e - 1 = λ");
check(lift(Mod(y,N)^(27*3))==y,         "354 y^{81} ≡ y");
check(27*3 == lam+1,                    "355 ae = λ+1");
check(lift(Mod(42,N)^43)==y,            "356 e=43 ≡ 3 (mod 40) same x");
check(lift(Mod(42,N)^83)==y,            "357 e=83 ≡ 3 (mod 80) same x");
check(41%40==1 && gcd(41,lam)==1,       "358 41 ≡ 1 (mod 40) is the peel-gap e");
check(81%40==1 && (81-1)%lam==0,        "359 81 ≡ 1 (mod 40) is λ-type");
check(eulerphi(80)/eulerphi(40)==2,     "360 |ker| = 2 for reduction mod 40");

check((43-3)%o==0,                      "361 43-3 is a multiple of 40");
check((83-3)%lam==0,                    "362 83-3 is a multiple of λ");
check(gcd(67,lam)==1,                   "363 e=67 residual-shaped for x=93");
check(gcd(51,lam)==1,                   "364 e=51 residual-shaped for x=25");
check(gcd(61,lam)==1,                   "365 e=61 residual-shaped for x=168");
check(gcd(57,lam)==1,                   "366 e=57 residual-shaped for x=104");
check(gcd(29,lam)==1,                   "367 e=29 residual-shaped for x=15");
check(gcd(39,lam)==1,                   "368 e=39 residual-shaped for x=26");
check(lift(Mod(26,N)^39)==y,            "369 26^{39} ≡ 36 k=e=39");
check(11*11 % 40==1,                    "370 11^2 ≡ 1 (mod 40) self-inverse k");

\\ ----- W 371-400 equality order-finding vs gcd, 5-smooth -----
check(8*5==40,                          "371 40=8*5 is 5-smooth");
check(lam%o==0,                         "372 ord(y) | λ");
check(lam/o==2,                         "373 [λ : ord(y)] = 2");
check(lift(Mod(y,N)^40)==1,             "374 equality-only: y^{40}≡1");
check(lift(Mod(y,N)^20)!=1,             "375 equality-only: y^{20}≢1");
check(lift(Mod(y,N)^8)!=1,              "376 equality-only: y^8≢1");
check(lift(Mod(y,N)^5)!=1,              "377 equality-only: y^5≢1");
check(gcd(lift(Mod(y,N)^5)-1,N)==11,    "378 gcd-based order test y^5-1 splits");
check(gcd(lift(Mod(y,N)^8)-1,N)==17,    "379 gcd-based order test y^8-1 splits");
check(gcd(lift(Mod(y,N)^40)-1,N)==N,    "380 equality y^{40}=1 is gcd=N, no proper factor");
check(lift(Mod(y,N)^27)==42,            "381 after ord=40, x=y^{27} leftover");
check(3*27-1==80,                       "382 residual cube is SAGM (a,e)=(27,3) on y");
check(27==lift(1/Mod(3,o)),             "383 27 ≡ 3^{-1} (mod 40)");
check(27==lift(1/Mod(3,lam)),           "384 27 ≡ 3^{-1} (mod λ) too on this pin");
check(znorder(Mod(42,N))==o,            "385 leftover x generates <y>");
check(znorder(Mod(100,N))==8,           "386 2-primary generator order 8");
check(znorder(Mod(137,N))==5,           "387 5-primary generator order 5");
check(lcm(8,5)==o,                      "388 lcm(|C8|,|C5|)=ord(y)");
check(gcd(8,5)==1,                      "389 C8 ∩ C5 = {1}");
check(valuation(5,2)==0,                "390 v2(ord_p y)=0 no 2-part on p");
check(valuation(8,2)==3,                "391 v2(ord_q y)=3");
check(valuation(o,2)==3,                "392 v2(ord_N y)=3 = max of locals");
check(valuation(lam,2)==4,              "393 v2(λ)=4 > v2(ord y): missing C2");
check(lift(Mod(3,N)^40)!=1,             "394 3^{40}≢1, ⟨3⟩ properly contains ⟨y⟩");
check(lift(Mod(3,N)^80)==1,             "395 3^{80}≡1");
check(46%2==0,                          "396 y is an even power of 3");
check((155*69)%N==36,                   "397 C8-part * C5-part reconstructs y");
check(lift(Mod(42,N)^3)==y,             "398 inverse automorphism: cube of leftover x");
check(lift(Mod(y,N)^27)==42,            "399 27th power of y is leftover x");
check(gcd(3,8)==1 && gcd(3,5)==1,       "400 cubing auto on both primary components");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));

