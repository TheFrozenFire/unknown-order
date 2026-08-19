\\ Sampled-τ powers in (Z/NZ)*.  Mirrors PowersOfTau.v.
\\ N = 11*17, g = 3, contributors τ1=3, τ2=7, product 21 (invertible mod 80).

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

N = 11*17;
g = 3;
tau1 = 3;
tau2 = 7;
tau = tau1*tau2;
ordg = znorder(Mod(g, N));
check(ordg == 80, "znorder(3 mod 187) = 80");
check(gcd(tau, ordg) == 1, "τ coprime to ord(g) so it has an inverse");
tinv = lift(1/Mod(tau, ordg));
check((tau*tinv) % ordg == 1, "τ⁻¹ mod ord(g) exists");

pot(i) = lift(Mod(g, N)^(tau^i));
check(pot(0) == g % N, "P_0 = g");
check(pot(1) == lift(Mod(g, N)^tau), "P_1 = g^τ  (DL witness is τ)");
succ_ok = 1;
for(i = 0, 4, \
  if(lift(Mod(pot(i), N)^tau) != pot(i+1), succ_ok = 0) \
);
check(succ_ok, "P_{i+1} = P_i^τ for i=0..4");

\\ contribution multiplies the secret
contrib_ok = 1;
for(i = 0, 4, \
  left = lift(Mod(lift(Mod(g, N)^(tau1^i)), N)^(tau2^i)); \
  right = pot(i); \
  if(left != right, contrib_ok = 0) \
);
check(contrib_ok, "P_i after τ2-update of a τ1-string is g^{(τ1 τ2)^i}");

\\ a third contributor
tau3 = 11;
prod3 = tau1*tau2*tau3;
three_ok = 1;
for(i = 0, 3, \
  after2 = lift(Mod(lift(Mod(g, N)^(tau1^i)), N)^(tau2^i)); \
  after3 = lift(Mod(after2, N)^(tau3^i)); \
  want = lift(Mod(g, N)^(prod3^i)); \
  if(after3 != want, three_ok = 0) \
);
check(three_ok, "three contributions multiply: final τ = τ1 τ2 τ3");

\\ honest party moves the string
check(lift(Mod(g, N)^(tau1*tau2)) != lift(Mod(g, N)^tau2), "honest tau1 != 1 changes P_1");

\\ backward walker is τ⁻¹, not a public RSA e
walk_ok = 1;
for(i = 0, 4, \
  if(lift(Mod(pot(i+1), N)^tinv) != pot(i), walk_ok = 0) \
);
check(walk_ok, "raising to τ⁻¹ walks the chain backward");
e_pub = 3;
pub_walks = 1;
for(i = 0, 4, \
  if(lift(Mod(pot(i+1), N)^e_pub) != pot(i), pub_walks = 0) \
);
check(pub_walks == 0, "public RSA e=3 does not walk this chain");

\\ equal-DL completeness (Chaum–Pedersen equations)
w = 4; c = 5;
h = lift(Mod(g, N)^tau);
u = h;
v = lift(Mod(u, N)^tau);
t1 = lift(Mod(g, N)^w);
t2 = lift(Mod(u, N)^w);
z = w + c*tau;
check(lift(Mod(g, N)^z) == (t1 * lift(Mod(h, N)^c)) % N, "eqDL g-side");
check(lift(Mod(u, N)^z) == (t2 * lift(Mod(v, N)^c)) % N, "eqDL u-side");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
