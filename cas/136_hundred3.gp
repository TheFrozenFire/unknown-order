\\ Third hundred: residual leaf, Pohlig on mismatched local orders.
\\ CAS↔Rocq crosswalk: notes/hundred3.md.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; lam=pin_lam; y=pin_y; x=pin_x; e=pin_e; o=40;

\\ ----- N 201-220 residual output language -----
check(lift(Mod(x,N)^o)==1,              "201 42^{40} ≡ 1 in <y>");
check(znorder(Mod(x,N))==o,             "202 ord(42)=40 generator");
check(lift(Mod(y,N)^27)==x,             "203 36^{27} ≡ 42");
check(gcd(27,o)==1,                     "203 gcd(27,40)=1");
check(lift(Mod(1,N)^3)==1,              "204 1^3 ≡ 1");
check(lift(Mod(67,N)^3)==67,            "204 67^3 ≡ 67 not 1");
check(lift(Mod(x,N)^3)==y,              "205 unique cube 42^3 ≡ 36");
check(gcd(e,16)==1,                     "206 e=3 invertible mod 16");
check(gcd(e,5)==1,                      "207 e=3 invertible mod 5");
check(27%16==11 && 27%5==2,             "208 27 ≡ (11,2) (mod 16,5)");
check(lift(chinese(Mod(11,16),Mod(2,5)))==27, "208 CRT inverse of 3 is 27");
check(gcd(5,lam)==5,                    "209 5|λ so e=5 is not residual");
check(kronecker(x,N)==1 && kronecker(y,N)==1, "210 Jacobi(x)=Jacobi(y)=+1");
check(issquare(Mod(x,p)) && issquare(Mod(x,q)), "211 42 is QR mod p and mod q");
check(znorder(Mod(2,N))==40,            "212 ord(2)=40");
found=0; for(k=0,40, if(lift(Mod(2,N)^k)==x, found=1));
check(found==0,                         "212 42 not in <2>");
check(lift(Mod(3,N)^42)==x,             "213 3^{42} ≡ 42");
check(lift(Mod(5,N)^34)==x,             "213 5^{34} ≡ 42");
check(x%p==9,                           "214 42 ≡ 9 (mod 11) local cube root");
check(lift(Mod(9,p)^3)==y%p,            "214 9^3 ≡ 36 (mod 11)");
check(x%q==8,                           "215 42 ≡ 8 (mod 17)");
check(lift(chinese(Mod(9,p),Mod(8,q)))==x, "216 CRT(9,8)=42");
check(x==32+8+2,                        "217 42=2^5+2^3+2^1");
check(x%8==2,                           "218 42 ≡ 2 (mod 8)");
check(gcd(x-1,N)==1 && isprime(x-1),    "219 x-1=41 prime, no split");
check(gcd(x+1,N)==1 && isprime(x+1),    "220 x+1=43 prime, no split");

\\ ----- O 221-240 generators and non-generators of <y> -----
check(eulerphi(o)==16,                  "221 phi(40)=16 generators");
check(gcd(2,o)==2,                      "222 k=2 shares 40, not a generator");
check(lift(Mod(y,N)^2)==174,            "222 y^2 ≡ 174");
check(znorder(Mod(174,N))==20,          "222 ord(174)=20");
check(gcd(lift(Mod(174,N)^3)-y,N)==11,  "222 174^3 one-sided split");
check(lift(Mod(y,N)^20)==67,            "223 y^{20} ≡ 67 order 2");
check(lift(Mod(67,N)^2)==1,             "223 67^2 ≡ 1 Miller");
check(lift(Mod(y,N)^16)==69,            "224 y^{16} ≡ 69 order 5");
check(lift(Mod(69,N)^5)==1,             "224 69^5 ≡ 1");
check(lift(Mod(y,N)^8)==137,            "225 y^8 ≡ 137");
check(lift(Mod(137,N)^5)==1,            "225 137^5 ≡ 1");
check(lift(Mod(y,N)^32)==86,            "226 y^{32} ≡ 86");
check(gcd(lift(Mod(86,N)^3)-y,N)==11,   "226 86^3 one-sided split");
check(lift(Mod(y,N)^5)==100,            "227 y^5 ≡ 100 ord 8");
check(znorder(Mod(100,N))==8,           "227 ord(100)=8 not generator");
check(lift(Mod(y,N)^10)==89,            "228 y^{10} ≡ 89 order 4");
check(lift(Mod(1,N)^3)==1 && 1!=y,      "229 1 is not a root of 36");
check(lift(Mod(y,N)^35)==144,           "230 y^{35} ≡ 144");
check(gcd(lift(Mod(144,N)^3)-y,N)==17,  "230 144^3 one-sided split");
check(lift(Mod(y,N)^4)==169,            "231 y^4 ≡ 169 order 10, not a generator");
check(gcd(4,o)==4,                      "231 gcd(4,40)=4");
check(gcd(x-9,N)==11,                   "232 gcd(42-9,N)=11 generator pair");
check(gcd(x-53,N)==11,                  "233 gcd(42-53,N)=11");
check(gcd(x-93,N)==17,                  "234 gcd(42-93,N)=17");
check(gcd(y-x,N)==1,                    "235 gcd(36-42,N)=1");
check(lift(Mod(y,N)^39)==26,            "236 y^{39} ≡ 26 = y^{-1}");
check(lift(Mod(y,N)*Mod(26,N))==1,      "236 36*26 ≡ 1");
check(lift(Mod(y,N)^13)==49,            "237 y^{13} ≡ 49 = x^{-1}");
check(lift(Mod(x,N)*Mod(49,N))==1,      "237 42*49 ≡ 1");
check(lift(Mod(y,N)^29)==15,            "238 y^{29} ≡ 15");
check(lift(Mod(y,N)^3)==93,             "239 y^3 ≡ 93 generator k=3");
check(gcd(3,o)==1,                      "239 gcd(3,40)=1");
check(lift(Mod(y,N)^9)==70,             "240 y^9 ≡ 70 generator k=9");

\\ ----- P 241-260 Pohlig on y / periods -----
check(gcd(lift(Mod(y,N)^5)-1,N)==11,    "241 gcd(y^5-1,N)=11 ord_p");
check(gcd(lift(Mod(y,N)^8)-1,N)==17,    "242 gcd(y^8-1,N)=17 ord_q");
check(gcd(lift(Mod(y,N)^10)-1,N)==11,    "243 gcd(y^{10}-1,N)=11");
check(gcd((y^4+1)%N, N)==17,            "244 gcd(y^4+1,N)=17");
check(gcd((y^2+1)%N, N)==1,             "245 gcd(y^2+1,N)=1");
check((y^4+y^3+y^2+y+1)%N==99,          "246 Phi_5(y) ≡ 99");
check(gcd(99,N)==11,                    "246 gcd(Phi_5(y),N)=11");
check(gcd(x^2-1,N)==1,                  "247 gcd(x^2-1,N)=1 residual x");
check(gcd(lift(Mod(y,N)^40)-1,N)==N,    "248 gcd(y^{40}-1,N)=N no proper factor");
check(gcd(67-1,N)==11,                  "249 Miller 67-1 splits");
check(y%p==3 && lift(Mod(3,p)^5)==1,    "250 ord_p(y)=5 : 3^5 ≡ 1 (mod 11)");
check(y%q==2 && lift(Mod(2,q)^8)==1,    "250 ord_q(y)=8 : 2^8 ≡ 1 (mod 17)");
check(o%5==0,                           "251 5 | ord(y)");
check(o%8==0,                           "252 8 | ord(y)");
check(znorder(Mod(3,N))==2*o,           "253 [⟨3⟩:⟨y⟩]=2");
check(46%2==0,                          "254 dl_3(y)=46 even");
check(lift(Mod(3,N)^46)==y,             "255 y = 3^{46} in ⟨3^2⟩");
check(gcd(5,lam)==5,                    "256 advice 5|λ");
check(valuation(lam,2)==4,              "257 v2(λ)=4");
check(lam%o==0,                         "258 40 | 80");
check(lift(Mod(y,N)^o)==1,              "259 y^{40} ≡ 1");
check(eulerphi(N)/lam==2,               "260 φ/λ=2");

\\ ----- Q 261-280 advice and program shapes -----
check(lam != N-1,                       "261 λ ≠ N-1");
check(lam%o==0,                         "262 40 | 80");
check(gcd(e,10)==1 && gcd(e,16)==1,     "263 e coprime to 10 and 16");
check(e%5!=0,                           "264 5 does not divide e=3");
check(kronecker(y,N)==1,                "265 y is Jacobi +1");
check(x%p==9,                           "266 advice local root 9");
check(N%o==27,                          "267 N ≡ 27 ≡ d (mod 40)");
check(2^6 <= lam && lam < 2^7,          "268 bitlength λ is 7");
check(gcd(p-1,q-1)==2,                  "269 gcd(p-1,q-1)=2");
check(lcm(p-1,q-1)==lam,                "270 λ=lcm(10,16)");
check(lift(Mod(y,N)^27)==x && gcd(27,o)==1, "271 x=y^{e^{-1} mod 40}");
check(N%o==27,                          "272 public k=N mod 40 hits 27");
check(lift(Mod(y,N)^27)==x,             "273 y^d ≡ x decrypt");
check(lift(Mod(y,N)^1)==y,              "274 k=1 is y, not the cube root");
check(lift(Mod(y,N)^3)==93 && 93!=x,    "275 k=3 is y^3, not the cube root");
check(gcd(lift(Mod(y,N)^5)-1,N)==11,    "276 public d=5 | 40 Pohlig splits");
check(gcd(x-y,N)==1,                    "277 Euclid(x-y,N)=1");
check(y%4==0,                           "278 low 2 bits of y are 00");
check(gcd(2,o)==2,                      "279 even k cannot give a generator");
check(lift(Mod(26,N)^79)==y,            "280 y^{-1} with e=λ-1 leftover");

\\ ----- R 281-300 CRT, Hensel, sqrt-poly, local orders -----
check(lift(chinese(Mod(9,p),Mod(8,q)))==x, "281 CRT of locals is the residual x");
check((x^3)%(p^2)==y%(p^2),             "282 Hensel: 42^3 ≡ 36 (mod 121)");
check((256+y)%N==105,                   "283 pad 2^8+y ≡ 105");
check(lift(Mod(105,N)^3)==95,           "283 105^3 ≡ 95 not 36");
check(6*7==42 && 6^2==y,                "284 integer sqrt then n(n+1)=x leftover");
check(lift(Mod(42,N)^3)==y,             "284 that x is the cube root");
check(gcd(6,N)==1,                      "285 integer sqrt is a unit, even peel no split");
check(27%10==7,                         "286 d_p = d mod (p-1) =7");
check((3*7-1)%10==0,                    "287 e d_p-1 is a multiple of p-1");
check(27%16==11,                        "288 d_q = d mod (q-1)=11");
check((3*11-1)%16==0,                   "289 e d_q-1 is a multiple of q-1");
check(isprime(e),                       "290 residual e=3 is prime");
check(lift(Mod(y,N)^2)==174,            "291 binary cube: y^2 ≡ 174");
check(lift(Mod(y,N)^3)==93,             "291 y^3 ≡ 93 encrypt, not invert");
check((y*256)%N==53,                    "292 Montgomery-ish y R ≡ 53");
check(isprime(7) && lift(Mod(60,N)^7)==y, "293 next prime e=7 leftover");
check(gcd(3,7)==1,                      "294 Shamir 3,7 coprime");
check((42*15)%N==69,                    "295 42 * 25^{-1} ≡ 69 order 5");
check(znorder(Mod(69,N))==5,            "295 ratio of leftover generators is 5-torsion");
check((42*53)%N==169,                   "296 42 * 60^{-1} ≡ 169 = y^4");
check(lift(Mod(84,N)^3)==(y*8)%N,       "297 rerand (2x)^3 ≡ y 2^3");
check(lift(Mod(x,N)^8)==69,             "298 x^8 ≡ 69 the 5-torsion");
check(lift(Mod(3,p)^5)==1 && lift(Mod(2,q)^8)==1, "299 mismatched local orders of y");
check(lcm(5,8)==o,                      "300 lcm(ord_p y, ord_q y)=ord_N y");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
