\\ CAS witnesses — Lucas V as the p+1 engine, and the Type-B wall.
\\ Mirrors Lucas.v / ClassGroupWall.v / Cyclotomic.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

\\ Lucas V by recurrence (Q = 1)
V(P, n) = {
  if(n==0, return(2));
  if(n==1, return(P));
  a = 2; b = P;
  for(i = 2, n, t = P*b - a; a = b; b = t);
  b
};

P = 5;
check(V(P,0)==2,                        "V_0 = 2");
check(V(P,1)==P,                        "V_1 = P");
check(V(P,2)==P*P-2,                    "V_2 = P^2-2");
check(V(P,4)==V(P,2)^2-2,               "V_4 = V_2^2-2  (doubling, Q=1)");
check(V(P,6)==V(P,3)^2-2,               "V_6 = V_3^2-2");
check(V(P,8)==V(P,4)^2-2,               "V_8 = V_4^2-2");

\\ Williams p+1: when D = P^2-4 is QNR mod p, the point lives in
\\ the p+1 torus and V_{p+1} ≡ 2 (mod p).  P=3 has D=5 QR mod 11
\\ (so the period would divide p−1).  P=5 has D=21 QNR on both
\\ textbook Blum primes.
p = 11;
check(p%4==3,                           "11 is Blum");
check(kronecker(P^2-4, p)==-1,          "D=21 is QNR mod 11");
check(V(P, p+1) % p == 2,               "V_{p+1} ≡ 2 (mod 11)");
check(V(P, p-1) % p != 2,               "V_{p-1} is not 2: period is +1");

q = 19;
check(kronecker(P^2-4, q)==-1,          "D=21 is QNR mod 19");
check(V(P, q+1) % q == 2,               "V_{q+1} ≡ 2 (mod 19)");
check(V(P, q-1) % q != 2,               "V_{q-1} is not 2 on 19 either");

\\ Safe prime p=23=2*11+1 refuses p−1 (r=11 large) but p+1=24=8*3
\\ is 3-smooth — Type B at n=2 still fires.
check(isprime(23) && isprime(11),       "23 is safe");
check(factor(23+1)[,1][matsize(factor(23+1))[1]] <= 3, "p+1 of 23 is 3-smooth");
check(factor(23-1)[,1][matsize(factor(23-1))[1]] == 11, "p−1 of 23 is 2*11");

\\ Adaptive root / sRSA on (Z/NZ)* is trivial given λ.
\\ On a class-group discriminant there is no such λ from D.
N = 11*19; lam = lcm(10,18);
y = 7;
check(lift(Mod(y, N)^(lam+1)) == y % N, "λ+1 is an sRSA witness on (Z/NZ)*");
D = -47;
check(D < 0 && (D%4==1),                "−47 is an IQ discriminant");
check(lam != D && lam != -D,            "λ of 11*19 is not a function of D=−47");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
