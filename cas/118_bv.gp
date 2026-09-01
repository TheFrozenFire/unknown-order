\\ Boneh-Venkatesan: one-query e=3 unwind of an algebraic FACT≤RSA reduction.
\\ Mirrors BonehVenkatesan.v.
\\ A reduction that queries an integer cube can drop GRoot; the oracle was unnecessary.
\\ This is not a claim that RSA is easier than factoring.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

N = 11*17;

\\ integer cube: GRoot(8) = 2 over Z
check(2^3 == 8,                         "2^3 = 8  integer cube");
check(3^3 == 27,                        "3^3 = 27");
check(4^3 == 64,                        "4^3 = 64");
check(36 != 27 && 36 != 64,             "36 is not an integer cube");

\\ unwind: program [GConst 8; GRoot; GConst 11] outputs 11, a factor
\\ dropping GRoot and writing GConst 2 still outputs 11
check(gcd(11, N) == 11,                 "output 11 is a factor");
check(1 < 11 && 11 < N,                 "proper");

\\ a reduction that queries GRoot(36) over Z cannot replace it by an integer
\\ cube (36 is not a cube); 42^3 = 74088 ≠ 36
check(42^3 == 74088,                    "42^3 in Z is 74088, not 36");
check(lift(Mod(42,N)^3) == 36,          "42^3 ≡ 36 (mod N) only");

\\ query of a handle that is 0 mod 11 not mod 17 is already the leak
check(gcd(88, N) == 11,                 "GRoot of a leaked handle is unnecessary");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
