\\ CAS witnesses — Miller successive-squaring from M = ed−1.
\\ Mirrors Miller.v: M = 2^s * t, g0 = a^t, g_{i+1} = g_i^2,
\\ first nontrivial square root of 1 splits N.
\\ On the textbook instance M=80=16*5, a=2: 32, 89, 67, 1 and gcd(66,187)=11.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

oddpart(n) = { while(n%2==0, n = n/2); n };
val2(n) = valuation(n, 2);

miller_factor(N, M, a) = {
  t = oddpart(M); s = val2(M);
  g = lift(Mod(a,N)^t);
  if(g==1, return(0));
  for(i = 1, s, \
    ng = lift(Mod(g,N)^2); \
    if(ng==1, \
      if(g!=1 && g!=N-1, return(gcd(g-1, N)), return(0)) \
    ); \
    g = ng \
  );
  0
};

N = 187; M = 80;
check(oddpart(M) == 5,                  "t = 5");
check(val2(M) == 4,                     "s = 4");
check(lift(Mod(2,N)^5) == 32,           "g0 = 2^5 = 32");
check(lift(Mod(32,N)^2) == 89,          "32² ≡ 89");
check(lift(Mod(89,N)^2) == 67,          "89² ≡ 67");
check(lift(Mod(67,N)^2) == 1,           "67² ≡ 1");
check(67 != 1 && 67 != N-1,             "67 ≢ ±1 (mod N)");
check(gcd(67-1, N) == 11,               "gcd(66,187) = 11");
check(miller_factor(N, M, 2) == 11,     "miller_factor(2) = 11");

\\ every unit base either splits or is a strong liar; at least half split
split = 0; units = 0;
for(a = 2, N-2, \
  if(gcd(a,N)==1, \
    units++; \
    f = miller_factor(N, M, a); \
    if(f>1 && f<N && N%f==0, split++) \
  ) \
);
check(split * 2 >= units,               "≥ 1/2 of units split N=187 (exhaustive)");
printf("  [density] %d / %d units split\n", split, units);

\\ a second modulus
p = 61; q = 53; N2 = p*q; e = 17; d = lift(1/Mod(e, lcm(p-1,q-1)));
M2 = e*d - 1;
f2 = 0;
for(a = 2, 40, \
  if(gcd(a,N2)==1, \
    f = miller_factor(N2, M2, a); \
    if(f>1 && f<N2, f2=f; break) \
  ) \
);
check(f2==p || f2==q,                   "Miller finds a factor of 61*53");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
