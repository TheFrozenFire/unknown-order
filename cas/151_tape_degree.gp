\\ Nodiv tape degree: GConst 0, add/sub max, mul adds.
\\ e=3 and deg P ≤ 3 ⇒ deg(P^3−X) ≤ 9 < 10 = p−1.
\\ Squaring twice is deg 4, out of the window; X^27 is out.
\\ Mirrors ZPoly degree lemmas / GenericRing gra_deg_bound.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p=11; N=p*17;

check(poldegree(x)==1,                      "deg X = 1");
check(poldegree(x*x)==2,                    "deg(X·X)=deg X + deg X");
check(poldegree(x^3)==3,                    "deg(X^3)=3·deg X");
check(poldegree(x^3 - x)==3,                "deg(X^3−X)=3");
check(poldegree((x^2)^3 - x)==6,            "deg((X^2)^3−X)=6 < 10");
check(poldegree((x^3)^3 - x)==9,            "deg((X^3)^3−X)=9 < 10");
check(3*3 < p-1,                            "e·deg P = 9 < p−1 for deg P ≤ 3");
check(poldegree((x^4)^3 - x)==12,           "deg((X^4)^3−X)=12 not < 10");
check(3*4 >= p-1,                           "two squarings leave the window");
check(poldegree(x^27)==27,                  "deg(X^27)=27");
check(27 >= p-1,                            "trapdoor X^27 is not low-degree");
check(poldegree(42^3 - x)==1,               "GConst: deg(c^3−X)=1 < 10");

\\ one mul X·X is bound 2; two muls X^2·X is bound 3; X^2·X^2 is bound 4
check(1+1==2,                               "GMul X X: deg bound 2");
check(2+1==3,                               "GMul X^2 X: deg bound 3");
check(2+2==4,                               "GMul X^2 X^2: deg bound 4, out");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
