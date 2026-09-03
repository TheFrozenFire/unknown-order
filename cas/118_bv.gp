\\ Boneh-Venkatesan: one-query e=3 unwind of an algebraic FACT≤RSA reduction.
\\ Mirrors BonehVenkatesan.v.
\\ A reduction that queries an integer cube can drop GRoot; the oracle was unnecessary.
\\ This is not a claim that RSA is easier than factoring.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N = pin_N;

\\ integer cube: GRoot(8) = 2 over Z
check(2^3 == 8,                         "2^3 = 8  integer cube");
check(3^3 == 27,                        "3^3 = 27");
check(4^3 == 64,                        "4^3 = 64");
check(36 != 27 && 36 != 64,             "36 is not an integer cube");

\\ tape: GConst 8, GRoot → 2, then 2^10-1, GInv = gcd(1023, N) = 11
btape = [0, 1, 36];
btape = concat(btape, [8]);
btape = concat(btape, [2]);
check(btape[5] == 2,                    "GRoot(8) = 2");
btape = concat(btape, [btape[5]*btape[5]]);
btape = concat(btape, [btape[6]*btape[6]]);
btape = concat(btape, [btape[7]*btape[7]]);
btape = concat(btape, [btape[8]*btape[6]]);
btape = concat(btape, [1]);
btape = concat(btape, [btape[9]-btape[10]]);
check(btape[9] == 1024,                 "2^10 = 1024");
check(btape[11] == 1023,                "2^10-1 = 1023");
check(gcd(btape[11], N) == 11,          "GInv of that handle is 11");
check(1 < 11 && 11 < N,                 "proper");
\\ unwind: GConst 2 in place of GRoot still yields 11
check(gcd(2^10-1, N) == 11,             "unwound GConst 2 still factors");

\\ a reduction that queries GRoot(36) over Z cannot replace it by an integer
\\ cube (36 is not a cube); 42^3 = 74088 ≠ 36
check(42^3 == 74088,                    "42^3 in Z is 74088, not 36");
check(lift(Mod(42,N)^3) == 36,          "42^3 ≡ 36 (mod N) only");

\\ query of a handle that is 0 mod 11 not mod 17 is already the leak
check(gcd(88, N) == 11,                 "GRoot of a leaked handle is unnecessary");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
