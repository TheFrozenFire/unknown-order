\\ Generic-group interpreter: multiply/invert/eq, no add.
\\ Mirrors GenericGroup.v.  Pin N = pin_N, start [1, y] with y=2.
\\ One-sided product eq-test: gcd(2^10-1, N)=11.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N = pin_N; y = 2;

\\ PARI 1-indexed: tape[1]=1, tape[2]=y
gtape = [1, y];
gtape = concat(gtape, [gtape[2]*gtape[2]]);
gtape = concat(gtape, [gtape[3]*gtape[3]]);
gtape = concat(gtape, [gtape[4]*gtape[4]]);
gtape = concat(gtape, [gtape[5]*gtape[3]]);
check(gtape[6] == 2^10,                 "GGM 2^10 by successive squares");
check(gcd(gtape[6]-gtape[1], N) == 11,  "eq-test gcd(2^10-1, N)=11");
check(lift(Mod(2,11)^10) == 1,          "2^{10} ≡ 1 (mod 11)");
check(lift(Mod(2,17)^10) != 1,          "2^{10} ≢ 1 (mod 17)");

\\ y*y*y from [1,y] with y=36: no add
ytape = [1, 36];
ytape = concat(ytape, [ytape[2]*ytape[2]]);
ytape = concat(ytape, [ytape[3]*ytape[2]]);
check(ytape[4] == 36^3,                 "GGM y*y*y");
check(length(ytape) == 4,               "no additive handle");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
