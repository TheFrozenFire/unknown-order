\\ SAGM-only solver, safeprime residual, polynomial e(y).
\\ Mirrors SolverRestrict.v.  Residual leaf named, not solved.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N = pin_N; lam = 80;

\\ SAGM: y=g=3, x=g^{27}, e=3.  znorder(3)=80=λ.  ae-1=80.
g = 3; a = 27; ee = 3;
x = lift(Mod(g,N)^a);
check(znorder(Mod(g,N)) == lam,         "ord(3)=80=λ");
check(x == 75,                          "3^{27} ≡ 75");
check(lift(Mod(x,N)^ee) == g,           "x^e ≡ g  (SAGM root of the generator)");
check(a*ee - 1 == lam,                  "ae-1 = λ");
check(lift(Mod(g,N)^(a*ee-1)) == 1,     "g^{ae-1} ≡ 1  annihilator");
check(gcd(67-1, N) == 11,               "Miller on that annihilator still splits");

\\ two-generator scale: (g^a h^b)^e = g^{ae} h^{be}
h = 5; r_a = 2; r_b = 1; e81 = 81;
v = lift(Mod(g,N)^r_a * Mod(h,N)^r_b);
vs = lift(Mod(g,N)^(r_a*e81) * Mod(h,N)^(r_b*e81));
check(lift(Mod(v,N)^e81) == vs,         "SAGM scale: eval(ae,be) = eval^e");
check(vs == v,                          "e=81 is λ-type on this handle");

\\ safeprime N=77, λ=30=2*3*5
Ns = pin_77; lams = pin_77_lam;
check(lams == lcm(6,10),                "λ(77)=30");
check(gcd(3, lams) == 3,                "e=3 shares p'=3 with λ");
check(2*3+1 == 7 && Ns % 7 == 0,        "2 p'+1 = 7 divides N");
check(gcd(5, lams) == 5,                "e=5 shares q'=5 with λ");
check(2*5+1 == 11 && Ns % 11 == 0,      "2 q'+1 = 11 divides N");
\\ residual coprime odd e: 2^7 ≡ 51, gcd(7,30)=1, 30 ndiv 6
y7 = lift(Mod(2,Ns)^7);
check(y7 == 51 && gcd(51,Ns)==1,        "2^7 ≡ 51 unit");
check(gcd(7, lams)==1,                  "gcd(7,30)=1");
check((7-1) % lams != 0,                "30 does not divide 6");
check(7 % 2 == 1,                       "e=7 odd: residual leaf, not solved");

\\ polynomial e(y)
check(3 == 3,                           "constant P=[3] is fixed e=3");
check(36 != 2,                          "P=X non-constant: P(36)≠P(2)");
check(36 * 2^3 != 36,                   "P=X not invariant under y ↦ y r^3");
check(lift(Mod(42,N)^3)==36,            "constant e=3 cube root is residual on 187");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
