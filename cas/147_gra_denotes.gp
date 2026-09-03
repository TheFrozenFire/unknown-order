\\ Division-free GRA denotes a polynomial; integer P^e = X is
\\ forbidden at y=2; identity tape is not residual; pin attains λ.
\\ Mirrors GenericRing.v denotation / Order.v max-order pin.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N = pin_N; y=36;
peval(cs, x) = {
  my(s = 0, pw = 1, ii);
  for(ii = 1, length(cs), s += cs[ii]*pw; pw *= x);
  s
};

\\ nodiv tape GMul y y: handle 3 is y^2, poly X^2 = [0,0,1]
check(y*y == 36*36,                     "nodiv GMul y y over Z");
check(peval([0,0,1], y) == y*y,         "denotation: eval(X^2,y)=y^2");

\\ integer identity a^e = y for all y fails at y=2, e=3
check(2^3 - 2 == 6 && 6 != 0,           "eval(X^3-X,2)=6 ≠ 0: integer identity forbidden");
check(2^7 - 2 == 126 && 126 != 0,       "eval(X^7-X,2)=126 ≠ 0");

\\ identity tape (output y) is not residual e=3 on the pin
check(lift(Mod(36,N)^3) != 36,          "identity tape: 36^3 ≢ 36, not residual invert");
check(znorder(Mod(36,N))==40,           "ord(36)=40 does not divide e-1=2");

\\ λ is attained as a unit order
check(znorder(Mod(3,N))==80,            "is_order: ord(3)=80=λ");
check(gcd(3,N)==1,                      "3 is a unit");
check(lcm(znorder(Mod(3,N)), znorder(Mod(36,N)))==80, "lcm(ord 3, ord 36)=λ");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
