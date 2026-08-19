\\ Cocks/BGH 1-bit pairing catalog.  Mirrors BGH.v.
\\ Williams pair p=11, q=23, N=253.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 11; q = 23; N = p*q;
check(p % 4 == 3 && q % 4 == 3, "Blum pair");
check(kronecker(-1, N) == 1, "Jacobi(-1/N)=+1 on Blum");

g = 3; check(gcd(g,N)==1, "g unit");
add_ok = 1;
for(a = 0, 12, \
  for(b = 0, 12, \
    left = kronecker(lift(Mod(g,N)^a), N) * kronecker(lift(Mod(g,N)^b), N); \
    right = kronecker(lift(Mod(g,N)^(a+b)), N); \
    if(left != right, add_ok = 0) \
  ) \
);
check(add_ok, "jacobi(g^a)*jacobi(g^b)=jacobi(g^{a+b})");

\\ Jacobi +1 is closed under multiply
closed_ok = 1;
for(a = 1, N-1, \
  if(gcd(a,N)==1 && kronecker(a,N)==1, \
    for(b = 1, N-1, \
      if(gcd(b,N)==1 && kronecker(b,N)==1, \
        if(kronecker(a*b, N) != 1, closed_ok = 0) \
      ) \
    ) \
  ) \
);
check(closed_ok, "Jacobi +1 is closed under multiply");

\\ Cocks pair: exactly one of {a,-a} is QR when Jacobi(a)=1
chosen_ok = 1;
for(a = 1, N-1, \
  if(gcd(a,N)==1 && kronecker(a,N)==1, \
    qr_a = (kronecker(a,p)==1 && kronecker(a,q)==1); \
    qr_na = (kronecker(-a,p)==1 && kronecker(-a,q)==1); \
    if(qr_a + qr_na != 1, chosen_ok = 0) \
  ) \
);
check(chosen_ok, "pair covers Blum: exactly one of {a,-a} is QR");

\\ decrypt identity on the square side
a = 3;
s = lift(sqrt(Mod(a, p)));
\\ find a global square root of a if it is QR, else of -a
if(kronecker(a,p)==1 && kronecker(a,q)==1, \
  sa = lift(chinese(Mod(lift(sqrt(Mod(a,p))), p), Mod(lift(sqrt(Mod(a,q))), q))); \
  aa = a, \
  sa = lift(chinese(Mod(lift(sqrt(Mod(-a,p))), p), Mod(lift(sqrt(Mod(-a,q))), q))); \
  aa = -a \
);
t = 5; tinv = lift(1/Mod(t, N));
c = (t + aa*tinv) % N;
check(kronecker(c + 2*sa, N) == kronecker(t, N), "Cocks decrypt on the square side");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
