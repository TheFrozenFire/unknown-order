\\ CAS witnesses — Williams torus mod N.  Mirrors Torus.v.
\\ Order is lcm(p+1,q+1), not λ and not N+1.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

V(P, n) = {
  if(n==0, return(2));
  if(n==1, return(P));
  a = 2; b = P;
  for(i = 2, n, t = P*b - a; a = b; b = t);
  b
};

p = 11; q = 19; N = p*q; P = 5;
check(kronecker(P^2-4, p)==-1,          "D=21 is QNR mod 11");
check(kronecker(P^2-4, q)==-1,          "D=21 is QNR mod 19");
check(V(P, p+1) % p == 2,               "V_{p+1} ≡ 2 (mod 11)");
check(V(P, q+1) % q == 2,               "V_{q+1} ≡ 2 (mod 19)");

tord = lcm(p+1, q+1);
lam = lcm(p-1, q-1);
check(tord == lcm(12,20),               "torus order lcm(12,20)=60");
check(lam == 90,                        "lambda is 90, not 60");
check((p+1)*(q+1) == N + (p+q) + 1,    "algebra: (p+1)(q+1)=N+p+q+1");
check(V(P, N+1) % N != 2,               "N+1 does not annihilate the torus");
check(V(P, tord) % p == 2,              "torus order annihilates mod p");
check(V(P, tord) % q == 2,              "torus order annihilates mod q");

\\ One-sided: M = p+1 annihilates mod p not mod q
M = p+1;
check(V(P, M) % p == 2,                 "one-sided V_M ≡ 2 (mod p)");
check(V(P, M) % q != 2,                 "one-sided V_M not 2 (mod q)");
g = gcd(V(P, M) - 2, N);
check(g == p || g == q || (g>1 && g<N), "one-sided gcd splits N");

\\ Fermat Type A: if we had p+q, torus period is public
s = p+q;
check((p+1)*(q+1) == N+s+1,            "Fermat sum yields torus period");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
