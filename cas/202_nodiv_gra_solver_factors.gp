\\ Nodiv GRA that inverts every unit denotes an invert-all-units
\\ poly, so Win B Miller-factors.  The y^d addition chain is nodiv
\\ and inverts; a square tape does not.  GInv is outside this class.
\\ Not residual-solver ⇒ factor.  Mirrors SrsaRootPoly.v.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; N=pin_N; e=pin_e; d=pin_d;

\\ y^2, y^4, y^8, y^16, y^24, y^26, y^27  (nodiv muls from handle y)
powd(yy) = {
  a2 = yy*yy;
  a4 = a2*a2;
  a8 = a4*a4;
  a16 = a8*a8;
  a24 = a16*a8;
  a26 = a24*a2;
  a26*yy
};

inv=1;
for(yy=1, N-1, \
  if(gcd(yy,N)==1, if(lift(Mod(powd(yy),N)^e)!=yy, inv=0)) \
);
check(inv,                              "nodiv y^d tape inverts every unit");
check(lift(Mod(powd(36),N)^e)==36,      "and inverts the pin challenge");
check(lift(Mod(powd(36),N))==lift(Mod(36,N)^d), "tape output is y^d");

g=gcd(2^10-1, N);
check(g==p,                             "Miller-from-d gcd is p");
check(1<g && g<N,                       "that gcd is a proper factor");

check(lift(Mod(2*2,N)^e)!=2,            "square tape misses unit 2");
check(lift(Mod(2,N)^e)!=2,              "identity tape misses unit 2");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
