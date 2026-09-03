\\ Dixon / QS combination: even exponent vectors make a square, then
\\ gcd splits N.  Pin N=187, factor base {2,3,5,7}.
\\ 24^2 ≡ 15 = 3·5, 37^2 ≡ 60 = 2^2·3·5; same parity (0,1,1,0);
\\ product 900 = 30^2; (24·37)^2 ≡ 30^2; gcd(140-30,187)=11.
\\ Already-even length-1: 14^2 ≡ 3^2 (Fermat-adjacent special case).
\\ Mirrors SieveRelation.v dixon_two_relations / dixon_24_37_splits.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

N = 11*17;
check(N == 187,                           "pin N=187");
check((24^2) % N == 15,                   "24^2 ≡ 15 (mod 187)");
check((37^2) % N == 60,                   "37^2 ≡ 60 (mod 187)");
check(15 == 3*5,                          "15 = 3·5");
check(60 == 2^2*3*5,                      "60 = 2^2·3·5");
check((15*60) == 30^2,                    "product of residues is 30^2");
check((24*37) % N == 140,                 "24·37 ≡ 140");
check((140^2) % N == (30^2) % N,          "(24·37)^2 ≡ 30^2 (mod 187)");
check(140 % N != 30 && 140 % N != N-30,   "140 ≢ ±30");
check(gcd(140-30, N) == 11,               "gcd(110,187)=11");
check(gcd(140+30, N) == 17,               "gcd(170,187)=17");

\\ length-1 even vector (already a square residue)
check((14^2) % N == 9,                    "14^2 ≡ 9 = 3^2");
check(gcd(14-3, N) == 11,                 "length-1: gcd(11,187)=11");

\\ second two-relation combo, same parity
check((38^2) % N == 135,                  "38^2 ≡ 135 = 3^3·5");
check((24*38) % N == 164,                 "24·38 ≡ 164");
check((15*135) == 45^2,                   "15·135 = 45^2");
check(gcd(164-45, N) == 17,               "second combo splits the other prime");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
