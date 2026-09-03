\\ QR mod N vs Jacobi, Blum exactly-one of {a,-a}, Jacobi degeneracy, Shamir (2,3).
\\ Mirrors QRModN.v.  Williams pair p=11, q=23, N=253.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p = pin_253_p; q = pin_253_q; N = pin_253;
check(p % 4 == 3 && q % 4 == 3, "Blum pair");
check(kronecker(-1, p) == -1 && kronecker(-1, q) == -1, "(-1/p)=(-1/q)=-1");
check(kronecker(-1, N) == 1, "Jacobi(-1/N)=+1");
check(kronecker(-1, p) != 1 || kronecker(-1, q) != 1, "-1 is not QR mod N");

\\ carefully chosen a: Jacobi +1, exactly one of {a,-a} is QR mod N
chosen_ok = 1; n_units = 0;
for(a = 1, N-1, \
  if(gcd(a,N)==1 && kronecker(a,N)==1, \
    n_units++; \
    qr_a = (kronecker(a,p)==1 && kronecker(a,q)==1); \
    qr_na = (kronecker(-a,p)==1 && kronecker(-a,q)==1); \
    if(qr_a + qr_na != 1, chosen_ok = 0) \
  ) \
);
check(n_units > 0, "some units with Jacobi +1");
check(chosen_ok, "Jacobi(a/N)=1 => exactly one of {a,-a} is QR mod N");

\\ Jacobi sees only parity
g = 3; check(gcd(g,N)==1, "g unit");
jg = kronecker(g, N);
parity_ok = 1;
for(k = 0, 20, \
  got = kronecker(lift(Mod(g,N)^k), N); \
  want = if(k % 2 == 0, 1, jg); \
  if(got != want, parity_ok = 0) \
);
check(parity_ok, "Jacobi(g^k/N) depends on k only mod 2");

\\ tail of g^{tau^i} has constant Jacobi
tau = 5; \\ odd
tail_odd = 1;
j1 = kronecker(lift(Mod(g,N)^tau), N);
for(i = 1, 5, \
  if(kronecker(lift(Mod(g,N)^(tau^i)), N) != j1, tail_odd = 0) \
);
check(tail_odd, "odd tau: Jacobi of g^{tau^i} constant for i>=1");
tau2 = 4; \\ even
tail_even = 1;
j1e = kronecker(lift(Mod(g,N)^tau2), N);
for(i = 1, 5, \
  if(kronecker(lift(Mod(g,N)^(tau2^i)), N) != j1e, tail_even = 0) \
);
check(tail_even, "even tau: Jacobi of g^{tau^i} constant for i>=1");
check(j1e == 1, "even tau => Jacobi of the tail is 1");

\\ Shamir at (2,3): square root and cube root of the same y give a 6th root
y = lift(Mod(2, N)^6);
s = lift(Mod(2, N)^3); \\ s^2 = 2^6 = y
c = lift(Mod(2, N)^2); \\ c^3 = 2^6 = y
check(lift(Mod(s,N)^2) == y, "s^2 = y");
check(lift(Mod(c,N)^3) == y, "c^3 = y");
w = lift(Mod(2, N)^1);
check(lift(Mod(w,N)^6) == y, "w^6 = y (sixth root from 2 and 3)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
