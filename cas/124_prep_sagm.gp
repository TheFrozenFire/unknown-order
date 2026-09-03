\\ Preprocessing GRA (advice on N, then generic ops on y) and SAGM reps.
\\ Mirrors PreprocessGRA.v / SAGM.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N = pin_N; y = 36;

\\ preprocessing advice is a function of N only
adv_factor = N / 17;
check(adv_factor == 11,                 "advice N/17 = 11 (depends on N, not y)");
check(gcd(adv_factor, N) == 11,         "that advice already factors N");
check(1 < 11 && 11 < N,                 "proper factor before looking at y");

adv_id = N;
check(gcd(adv_id, N) == N,              "advice N is not a proper factor");

\\ GRA after placing advice on the tape: GInv of the factor-advice
ptape = [0, 1, y, adv_factor];
check(gcd(ptape[4], N) == 11,           "GInv of advice handle returns 11");
check(ptape[3] == y,                    "y unused");

\\ SAGM: handle = g^a * h^b, product adds exponents
g = 3; h = 5;
a1 = 2; b1 = 1;
a2 = 1; b2 = 3;
v1 = lift(Mod(g,N)^a1 * Mod(h,N)^b1);
v2 = lift(Mod(g,N)^a2 * Mod(h,N)^b2);
vprod = lift(Mod(v1,N)*Mod(v2,N));
vsum = lift(Mod(g,N)^(a1+a2) * Mod(h,N)^(b1+b2));
check(v1 == lift(Mod(9,N)*Mod(5,N)),    "rep (2,1) evaluates");
check(vprod == vsum,                    "product of handles = sum of exponents");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
