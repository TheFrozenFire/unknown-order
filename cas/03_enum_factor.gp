\\ CAS witnesses — multiplier enumeration / quadratic recovery of {p,q}.
\\ Mirrors FactorEnum.v and NumberTheory.factors_from_phi.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

factors_from_phi(N, phi) = {
  s = N - phi + 1;
  disc = s^2 - 4*N;
  r = sqrtint(disc);
  [(s+r)/2, (s-r)/2]
};

\\ textbook instance: φ = 160 recovers {17,11}
N = 187; phi = 160;
pq = factors_from_phi(N, phi);
check(pq[1]*pq[2] == N,                 "product of recovered roots is N");
check(Set(pq) == Set([11,17]),          "roots are {11,17}");
check((11+17) == N - phi + 1,           "p+q = N−φ+1");

\\ when d is an inverse modulo φ (not just λ), k = (ed−1)/φ is an integer
p = 61; q = 53; N2 = p*q;               \\ Wikipedia textbook RSA
phi2 = (p-1)*(q-1);
e2 = 17; d2 = lift(1/Mod(e2, phi2));
k = (e2*d2 - 1) / phi2;
check(type(k) == "t_INT" && k > 0 && (e2*d2-1) % phi2 == 0, "phi divides ed-1");
pq2 = factors_from_phi(N2, (e2*d2-1)/k);
check(Set(pq2) == Set([p,q]),           "enum recovers {61,53} from (e,d) via φ");

\\ random small balanced primes, e=3
setrand(2);
enum_fail = 0;
for(t = 1, 40, \
  pp = nextprime(50 + random(150)); \
  qq = nextprime(50 + random(150)); \
  if(pp==qq, next); \
  if(pp<qq, tmp=pp; pp=qq; qq=tmp); \
  NN = pp*qq; ph = (pp-1)*(qq-1); \
  if(gcd(3,ph)!=1, next); \
  dd = lift(1/Mod(3, ph)); \
  rec = factors_from_phi(NN, (3*dd-1)/((3*dd-1)/ph)); \
  if(Set(rec) != Set([pp,qq]), enum_fail++) \
);
check(enum_fail == 0,                   "enum recovers factors on random e=3 instances");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
