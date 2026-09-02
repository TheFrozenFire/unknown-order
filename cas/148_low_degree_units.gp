\\ Low-degree P^e−X cannot vanish on all units of Z/NZ.
\\ Identity X^3−X has deg 3 < p−1=10; roots mod 11 are 0,1,10.
\\ Constants have linear coeff −1.  Mirrors SrsaResidualGRA.v.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p=11; q=17; N=p*q;
Q3 = x^3 - x;
check(poldegree(Q3)==3,                 "deg(X^3−X)=3");
check(3 < p-1,                          "3 < p−1=10: identity is low-degree on this pin");
check(3 < q-1,                          "3 < q−1=16");
roots11 = [];
for(a=0, p-1, if(lift(Mod(subst(Q3,x,a),p))==0, roots11 = concat(roots11,[a])));
check(roots11 == [0,1,10],              "X^3−X roots mod 11 are 0,1,10");
check(#roots11 - 1 == 2,                "at most two units among those roots");
check(lift(Mod(subst(Q3,x,2),p))!=0,    "2 is a unit of F_11 and not a root");
roots17 = [];
for(a=0, q-1, if(lift(Mod(subst(Q3,x,a),q))==0, roots17 = concat(roots17,[a])));
check(roots17 == [0,1,16],              "X^3−X roots mod 17 are 0,1,16");
check(lift(Mod(subst(Q3,x,2),q))!=0,    "2 is a unit of F_17 and not a root");

C42 = 42^3 - x;
check(polcoeff(C42,1)==-1,              "const 42: linear coeff of P^3−X is −1");
check(gcd(1,N)==1,                      "N does not divide −1");
check(lift(Mod(subst(Q3,x,36),N))!=0,   "pin y=36: X^3−X not 0 mod N");
check(lift(Mod(42,N)^3)!=8,             "constant leftover misses unit 8");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
