\\ Residual GRA dichotomy: residual-shaped e (odd, coprime to λ,
\\ λ ndiv e-1) vs AMS constant e=λ+1; GConst leftover misses a
\\ second unit; leading term e·deg P ≠ 1 + e·deg Q.
\\ Mirrors SrsaResidualGRA.v. Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p=11; q=17; N=p*q; lam=lcm(p-1,q-1); y=36; xx=42; e=3;
check(lam == 80,                        "λ=80");
check(e%2==1 && gcd(e,lam)==1 && (e-1)%lam!=0, "e=3 is residual-shaped");
check(lift(Mod(xx,N)^e)==y,             "leftover cube 42^3 ≡ 36");

e81 = lam+1;
check(e81 == 81,                        "λ+1=81");
check((e81-1)%lam==0,                   "e=81 is not residual: λ | e-1");
check(e81%2==1 && gcd(e81,lam)==1,      "e=81 is odd and coprime to λ (still not residual)");
check(gcd(e81, N)==1,                   "GConst 81 does not split N");
check(lift(Mod(y,N)^e81)==y,            "36^{81} ≡ 36");
check(lift(Mod(8,N)^e81)==8,            "8^{81} ≡ 8");
check(lift(Mod(2,N)^e81)==2,            "2^{81} ≡ 2");
units_ok = 1;
for(aa = 1, N-1, \
  if(gcd(aa,N)==1 && lift(Mod(aa,N)^e81)!=aa, units_ok = 0) \
);
check(units_ok == 1,                    "y^{81} ≡ y for every unit");

check(gcd(8,N)==1,                      "8 is a unit");
check(lift(Mod(42,N)^3)!=8,             "GConst 42 cubes to 36, not to unit 8");
check(lift(Mod(42,N)^3)!=2,             "GConst 42 does not cube to unit 2");

e7=7;
check(e7%2==1 && gcd(e7,lam)==1 && (e7-1)%lam!=0, "e=7 is residual-shaped");
check(e*0 != 1 + e*0,                   "leading e=3 const/const: 0 <> 1");
check(e*1 != 1 + e*0,                   "leading e=3 degP=1 degQ=0: 3 <> 1");
check(e*0 != 1 + e*1,                   "leading e=3 degP=0 degQ=1: 0 <> 4");
check(e7*0 != 1 + e7*0,                 "leading e=7 const/const: 0 <> 1");
check(e7*1 != 1 + e7*0,                 "leading e=7 degP=1 degQ=0: 7 <> 1");
check(e7*0 != 1 + e7*1,                 "leading e=7 degP=0 degQ=1: 0 <> 8");

\\ X^e − X linear coeff is −1 (N cannot divide every coeff)
XeX3 = x^3 - x;
XeX7 = x^7 - x;
check(polcoeff(XeX3,1)==-1,             "X^3−X linear coeff −1");
check(polcoeff(XeX7,1)==-1,             "X^7−X linear coeff −1");
check(gcd(1,N)==1,                      "N does not divide linear coeff −1");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
