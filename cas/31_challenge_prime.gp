\\ CAS witnesses — challenge encode ≠ slot encode; composite member splits.
\\ Mirrors ChallengePrime.v / Accumulator.v / ExpProof.v week 3.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

M = 103740; a = 13099;
check(2*0 + 1 == 1,                      "ch_encode(0) = 1");
check((2*0 + 1) % M != a,                "challenge image is not the constructor residue");

n_odd_pr = 0; all_odd = 1; all_on_ap = 1;
for(seed = 1, 30, ell = 2*seed + 1; if(ell%2!=1, all_odd=0); if(isprime(ell), n_odd_pr++; if(ell%M!=a, all_on_ap=0)));
check(all_odd,                           "challenge encode is odd");
check(n_odd_pr >= 3,                     "several odd primes in seeds 1..30");
check(!all_on_ap,                        "accepted challenges are not all on the constructor AP");

N = pin_N;
W = 2; x = 15;
A = lift(Mod(W, N)^x);
check(A == lift(Mod(2, N)^15),           "A = 2^15 (mod 187)");
check(lift(Mod(W, N)^15) == A,           "W is a witness for 15");
W3 = lift(Mod(W, N)^5);
W5 = lift(Mod(W, N)^3);
check(lift(Mod(W3, N)^3) == A,           "W^5 is a witness for 3");
check(lift(Mod(W5, N)^5) == A,           "W^3 is a witness for 5");

N2 = 11*19; x2 = 7; T = 6; ellc = 9;
Qc = 2^T \ ellc; rc = 2^T % ellc;
y2 = lift(Mod(x2, N2)^(2^T));
pic = lift(Mod(x2, N2)^Qc);
check((lift(Mod(pic, N2)^ellc) * lift(Mod(x2, N2)^rc)) % N2 == y2 % N2, "honest π still verifies at composite ℓ=9");
check(!isprime(ellc),                    "ℓ=9 is composite");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
