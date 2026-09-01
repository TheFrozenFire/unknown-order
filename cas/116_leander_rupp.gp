\\ Division-free low-e GRA (Leander-Rupp).
\\ Mirrors GenericRing.v wave 1.
\\ Pin N=187, e=3.  A polynomial solver for one y does not factor;
\\ a polynomial identity P^e = X is forbidden by a coeff ±1.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

N = 11*17; ee = 3;

peval(cs, x) = {
  my(s = 0, pw = 1, ii);
  for(ii = 1, length(cs), s += cs[ii]*pw; pw *= x);
  s
};

\\ degree table for e=3
XmX = [0, -1, 0, 1];
check(peval(XmX, 0) == 0,               "eval(X^3-X, 0) = 0");
check(peval(XmX, 1) == 0,               "eval(X^3-X, 1) = 0");
check(peval(XmX, 2) == 6,               "eval(X^3-X, 2) = 6");
check(XmX[2] == -1,                     "linear coeff of X^3-X is -1");
check(gcd(1, N) == 1,                   "N does not divide -1");

C42 = [42^3, -1];
check(C42[2] == -1,                     "const-42 Pe-X linear coeff -1");

\\ constant-42 GRA inverts y=36 and fails on y=8
check(lift(Mod(42,N)^ee) == 36,         "42^3 ≡ 36 (mod N)  inverts the test vector");
check(lift(Mod(42,N)^ee) != 8,          "42^3 ≢ 8 (mod N)  not a solver for all y");

\\ identity GRA: output y
check(lift(Mod(2,N)^ee) != 2,           "2^3 ≢ 2 (mod N)");
check(lift(Mod(1,N)^ee) == 1,           "1^3 ≡ 1, no split");
check(gcd(2^ee - 2, N) == 1,            "gcd(8-2, N)=1");

\\ 2 is not an integer cube (degree obstruction over Z)
check(0^ee != 2 && 1^ee != 2 && (-1)^ee != 2, "no |a|<=1 with a^3=2");
check(2^ee >= 4,                        "2^3 >= 4");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
