\\ GRA tape, Z[X] eval, equality-test gcd leak.
\\ Mirrors ZPoly.v / GenericRing.v wave 0.
\\ Pin N=11*17=187, e=3.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

N = 11*17;

\\ Horner, low term first (PARI 1-indexed)
peval(cs, x) = {
  my(s = 0, pw = 1, ii);
  for(ii = 1, length(cs), s += cs[ii]*pw; pw *= x);
  s
};

\\ X^3 - X = [0, -1, 0, 1]
XmX = [0, -1, 0, 1];
check(peval(XmX, 2) == 6,               "eval(X^3-X, 2) = 6");
check(XmX[2] == -1 && XmX[4] == 1,      "X^3-X coeffs 0,-1,0,1");
check(gcd(1, N) == 1,                   "N does not divide content of X^3-X");

\\ constant 42: 42^3 - X = [74088, -1]
C42 = [42^3, -1];
check(C42[1] == 74088 && C42[2] == -1,  "const 42: Pe-X = [74088, -1]");
check(peval(C42, 0) == 74088,           "eval(const42^3-X, 0) = 42^3");

\\ GRA tape over Z: init [0,1,y], GMul y y, GMul that y
\\ PARI 1-indexed: tape[1]=0, tape[2]=1, tape[3]=y
y = 36;
tape = [0, 1, y];
tape = concat(tape, [tape[3]*tape[3]]);
tape = concat(tape, [tape[4]*tape[3]]);
check(tape[5] == 36^3,                  "GRA y^3 over Z");
check(tape[5] % N == lift(Mod(36,N)^3), "GRA y^3 mod N");

\\ equality leak from a tape: build 88 from 1, gcd against handle 0
\\ Rocq: GAdd 1 1 → 2, GMul 3 3 → 4, GMul 4 3 → 8, GMul 4 4 → 16,
\\        GMul 6 4 → 64, GAdd 7 6 → 80, GAdd 8 5 → 88
etape = [0, 1, y];
etape = concat(etape, [etape[2]+etape[2]]);
etape = concat(etape, [etape[4]*etape[4]]);
etape = concat(etape, [etape[5]*etape[4]]);
etape = concat(etape, [etape[5]*etape[5]]);
etape = concat(etape, [etape[7]*etape[5]]);
etape = concat(etape, [etape[8]+etape[7]]);
etape = concat(etape, [etape[9]+etape[6]]);
check(etape[10] == 88,                  "tape handle 9 is 88");
check(etape[1] == 0,                    "tape handle 0 is 0");
check(gcd(etape[10]-etape[1], N) == 11, "gra_eq_gcd of those handles is 11");
check(88 % 11 == 0,                     "88 ≡ 0 (mod 11)");
check(88 % 17 != 0,                     "88 ≢ 0 (mod 17)");
check(1 < 11 && 11 < N,                 "proper factor");

\\ 0 ≡ 187 (mod N): gcd is N, not a split
check((0-187) % N == 0,                 "0 ≡ 187 (mod N)");
check(gcd(187, N) == N,                 "gcd is N, not a proper factor");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
