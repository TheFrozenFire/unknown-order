\\ Mixed cube roots of 1 split N=pq; diagonal leftover does not.
\\ x^3-1 = (x-1) Phi_3(x).  A mixed kernel element (1 on one prime,
\\ omega on the other) puts one prime in (x-1) and the other in Phi_3.
\\ Diagonal (omega on both) puts N in Phi_3 and gcd(x-1,N)=1.
\\ Small integer generators: Phi_3(3)=13, Phi_3(2)=7.
\\ Pin kernel {1}: no mixed leftover.  Mirrors CubicResidue.v
\\ mixed_mu3_splits / diagonal_mu3_no_split and EvalPairing.v
\\ gp_91_splits_N.  Named extra 13x7=91; pin 187.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p = pin_91_p; q = pin_91_q; N = pin_91;
om_p = pin_91_om_p; om_q = pin_91_om_q;
g_p = lift(chinese(Mod(om_p, p), Mod(1, q)));
g_q = lift(chinese(Mod(1, p), Mod(om_q, q)));
diag = lift(chinese(Mod(om_p, p), Mod(om_q, q)));
Phi3(x) = x*x + x + 1;

check(g_p == 29,                          "g_p = 29");
check(g_q == 79,                          "g_q = 79");
check(diag == 16,                         "diagonal CRT(3,2) = 16");
check((g_p^3 - 1) == (g_p-1)*Phi3(g_p),   "x^3-1 = (x-1) Phi_3(x) at g_p");
check(gcd(g_p-1, N) == q,                 "gcd(g_p-1, N) = q");
check(gcd(Phi3(g_p), N) == p,             "gcd(Phi_3(g_p), N) = p");
check(gcd(g_q-1, N) == p,                 "gcd(g_q-1, N) = p");
check(gcd(Phi3(g_q), N) == q,             "gcd(Phi_3(g_q), N) = q");
check(gcd(diag-1, N) == 1,                "diagonal: gcd(x-1, N) = 1");
check(gcd(Phi3(diag), N) == N,            "diagonal: gcd(Phi_3(x), N) = N");
check(Phi3(om_p) == p,                    "Phi_3(3) = 13 = p");
check(Phi3(om_q) == q,                    "Phi_3(2) = 7 = q");

ker_of(m) = {
  L = List();
  for(x = 1, m-1, if(gcd(x,m)==1 && lift(Mod(x,m)^3)==1, listput(L, x)));
  L
};
ker = ker_of(N);
check(#ker == 9,                          "9 kernel elements");

kind_count(L, m, want) = {
  c = 0;
  for(i = 1, #L, if(gcd(L[i]-1, m) == want, c++));
  c
};
check(kind_count(ker, N, N) == 1,         "one identity: gcd(x-1,N)=N");
check(kind_count(ker, N, p) + kind_count(ker, N, q) == 4, "four mixed: gcd(x-1,N) in {p,q}");
check(kind_count(ker, N, 1) == 4,         "four diagonal: gcd(x-1,N)=1");

both_primes(x, m) = gcd(x-1, m) != 1 && gcd(x-1, m) != m && gcd(x-1, m)*gcd(Phi3(x), m) == m;
n_both(L, m) = {
  c = 0;
  for(i = 1, #L, if(both_primes(L[i], m), c++));
  c
};
check(n_both(ker, N) == 4,                "each mixed sample returns both primes");

Npin = pin_N;
kpin = ker_of(Npin);
check(#kpin == 1,                         "pin kernel {1}");
check(kpin[1] == 1,                       "pin only residue is 1");
check(gcd(1-1, Npin) == Npin,             "pin: gcd(1-1,N)=N, no proper factor");
check(gcd(Phi3(1), Npin) == 1,            "pin: Phi_3(1)=3 coprime to 187");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
