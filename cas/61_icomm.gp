\\ Integer-commitment binding as a relation.  Mirrors Accumulator.v.
\\ C = g^x h^r.  Two openings with x>x' give g^{Δx} = h^{Δr}.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 11; q = 17; N = p*q;
g = 3; h = 9;
check(gcd(g,N)==1 && gcd(h,N)==1, "g,h units");
check(lift(Mod(h,N)) == lift(Mod(g,N)^2), "h = g^2 so Δx=2, Δr=1 binds");

x = 3; r = 1; xp = 1; rp = 2;
C  = lift(Mod(g,N)^x  * Mod(h,N)^r);
C2 = lift(Mod(g,N)^xp * Mod(h,N)^rp);
check(C == C2, "two openings of the same C");
check(lift(Mod(g,N)^(x-xp)) == lift(Mod(h,N)^(rp-r)), "g^{Δx} = h^{Δr}");
check(x-xp > 0, "this is a fractional-root witness, not the identity");

\\ same message, distinct randomness: annihilator of h
x0 = 4; r0 = 1; r1 = 3;
\\ h^{r1-r0} = h^2 = g^4, so pad g-side equally
C3 = lift(Mod(g,N)^x0 * Mod(h,N)^r0);
C4 = lift(Mod(g,N)^x0 * Mod(h,N)^r1);
\\ these are equal iff h^{2} = 1, which it is not. Use r1 = r0 + ord(h)
oh = znorder(Mod(h,N));
C5 = lift(Mod(g,N)^x0 * Mod(h,N)^(r0+oh));
check(C3 == C5, "same msg, randomness differs by ord(h)");
check(lift(Mod(h,N)^oh)==1, "that difference annihilates h");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
