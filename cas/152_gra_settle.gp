\\ Settle remaining GRA polish: exact deg(mul)/deg(P^e);
\\ short tapes X^2 and X^3 miss units (linear −1); trapdoor X^27
\\ inverts the pin but sits outside the low-degree window.
\\ Mirrors ZPoly exact degree / SrsaResidualGRA short tapes.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p=11; N=p*17;

check(poldegree(x*x)==poldegree(x)+poldegree(x), "exact: deg(X·X)=deg X+deg X");
check(polcoeff(x*x,2)==1,                      "leading of X^2 is 1·1");
check(poldegree((x^2)^3)==3*poldegree(x^2),    "exact: deg((X^2)^3)=3·deg(X^2)");
check(poldegree((x^2)^3-x)==6,                 "exact: deg(X^6−X)=6");
check(polcoeff(x^6-x,1)==-1,                   "X^6−X linear coeff −1");
check(polcoeff(x^9-x,1)==-1,                   "X^9−X linear coeff −1");

check(lift(Mod(subst(x^6-x,x,2),p))!=0,       "X^2 tape: unit 2 is not a root of X^6−X");
check(lift(Mod(subst(x^6-x,x,2),N))!=0,       "X^2 tape: 2^6−2 not 0 mod N");
check(lift(Mod(subst(x^9-x,x,2),p))!=0,       "X^3 tape: unit 2 is not a root of X^9−X");
check(lift(Mod(subst(x^9-x,x,2),N))!=0,       "X^3 tape: 2^9−2 not 0 mod N");
check((-1)%N != 0,                             "N does not divide linear −1");

check(lift(Mod(36,N)^27)==42,                  "trapdoor X^27 inverts pin y=36");
check(lift(Mod(42,N)^3)==36,                   "and cubes back: not forbidden as a map on units");
check(poldegree(x^27)>=p-1,                    "low-degree fork does not apply to X^27");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
