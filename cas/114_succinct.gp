\\ Logarithmic fold of the bilinear CRS combine.
\\ Mirrors Succinct.v.
\\ Posted proof is 13 log2(n) + 2 residues/integers, not one
\\ encoding per private slot.  Fold challenge x=2.
\\ Pin N = pin_N=187, g=3, tau=5.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N = pin_N; g = 3; tau = 5; Xch = 2;

evalp(cs, x) = {
  my(s = 0, p = 1, ii);
  for(ii = 1, length(cs), s += cs[ii]*p; p *= x);
  s
};
commit(cs) = lift(Mod(g, N)^evalp(cs, tau));

nextpow2(n) = {
  my(p = 1);
  while(p < n, p = 2*p);
  p
};
pad2(v) = {
  my(n = length(v), p = nextpow2(n));
  if(n == p, v, concat(v, vector(p-n, ii, 0)))
};
padto(v, p) = {
  my(n = length(v));
  if(n >= p, v, concat(v, vector(p-n, ii, 0)))
};
halves(v) = {
  my(m = length(v)/2);
  [vector(m, ii, v[ii]), vector(m, ii, v[m+ii])]
};
addx(v, w) = vector(length(v), ii, v[ii] + Xch*w[ii]);

quad_off(Ps, as, bs, off) = {
  my(acc = 1, ii, jj);
  for(ii = 1, length(as), \
    for(jj = 1, length(bs), \
      acc = (acc * lift(Mod(Ps[off+ii+jj-1], N)^(as[ii]*bs[jj]))) % N));
  acc
};

crs(nslots) = {
  my(Ps = vector(nslots), ii);
  for(ii = 0, nslots-1, Ps[ii+1] = lift(Mod(g, N)^(tau^ii)));
  Ps
};

\\ prove returns [rounds, ast, bst]
\\ each round: CAL CAR YA CBL CBR YB U L R W Ls Rs Ws  (13 residues)
\\ YA = g^{tau^m AR(tau)} binds CA = CAL * YA.
prove(as, bs) = {
  my(n = length(as));
  if(n == 1, return([[], as[1], bs[1]]));
  my(Ha = halves(as), Hb = halves(bs));
  my(aL = Ha[1], aR = Ha[2], bL = Hb[1], bR = Hb[2]);
  my(m = n/2);
  my(Ps = crs(2*n));
  my(CAL = commit(aL), CAR = commit(aR));
  my(CBL = commit(bL), CBR = commit(bR));
  my(YA = quad_off(Ps, aR, [1], m));
  my(YB = quad_off(Ps, bR, [1], m));
  my(U = quad_off(Ps, aL, bL, 0));
  my(L = quad_off(Ps, aL, bR, 0));
  my(R = quad_off(Ps, aR, bL, 0));
  my(W = quad_off(Ps, aR, bR, 0));
  my(Ls = quad_off(Ps, aL, bR, m));
  my(Rs = quad_off(Ps, aR, bL, m));
  my(Ws = quad_off(Ps, aR, bR, 2*m));
  my(a2 = addx(aL, aR), b2 = addx(bL, bR));
  my(tl = prove(a2, b2));
  [concat([CAL, CAR, YA, CBL, CBR, YB, U, L, R, W, Ls, Rs, Ws], tl[1]), tl[2], tl[3]]
};

proof_len(pr) = length(pr[1]) + 2;

verify(Ps, CA, CB, CAB, pr, nn) = {
  my(rnd = pr[1], ast = pr[2], bst = pr[3]);
  my(p = 1, ncur = nn, CAc = CA, CBc = CB, CABc = CAB);
  my(CAL, CAR, YA, CBL, CBR, YB, U, L, R, W, Ls, Rs, Ws, prod, P0);
  my(L2, R2, W4);
  while(ncur > 1, \
    CAL = rnd[p]; CAR = rnd[p+1]; YA = rnd[p+2]; \
    CBL = rnd[p+3]; CBR = rnd[p+4]; YB = rnd[p+5]; \
    U = rnd[p+6]; L = rnd[p+7]; R = rnd[p+8]; W = rnd[p+9]; \
    Ls = rnd[p+10]; Rs = rnd[p+11]; Ws = rnd[p+12]; \
    if((CAL * YA) % N != CAc, return(0)); \
    if((CBL * YB) % N != CBc, return(0)); \
    prod = (((U * Ls) % N * Rs) % N * Ws) % N; \
    if(prod != CABc, return(0)); \
    CAc = (CAL * lift(Mod(CAR, N)^Xch)) % N; \
    CBc = (CBL * lift(Mod(CBR, N)^Xch)) % N; \
    L2 = lift(Mod(L, N)^Xch); R2 = lift(Mod(R, N)^Xch); \
    W4 = lift(Mod(W, N)^(Xch*Xch)); \
    CABc = (((U * L2) % N * R2) % N * W4) % N; \
    p = p + 13; \
    ncur = ncur/2);
  P0 = Ps[1];
  lift(Mod(P0, N)^ast) == CAc && lift(Mod(P0, N)^bst) == CBc && lift(Mod(P0, N)^(ast*bst)) == CABc && ast >= 0 && bst >= 0
};

Cfold = 16;
count_n(n) = {
  my(k = 0, t = n);
  while(t > 1, t = t/2; k++);
  13*k + 2
};

a4 = [2, 3, 1, 0];
b4 = [1, 4, 0, 1];
a16 = [2, 3, 1, 0, 1, 0, 2, 1, 0, 3, 1, 0, 2, 0, 1, 0];
b16 = [1, 4, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 0, 1, 2, 1];
check(length(a4) == 4 && length(a16) == 16, "padded lengths 4 and 16");
check(length(a16) >= 4*length(a4), "n2 >= 4 n1");

Ps32 = crs(32);
pr4 = prove(a4, b4);
pr16 = prove(a16, b16);
len4 = proof_len(pr4);
len16 = proof_len(pr16);
printf("  proof_len n=4:  %d (bound %d = C log2 n)\n", len4, Cfold*2);
printf("  proof_len n=16: %d (bound %d = C log2 n)\n", len16, Cfold*4);
check(len4 == count_n(4), "n=4 length is 13 log2 n + 2");
check(len16 == count_n(16), "n=16 length is 13 log2 n + 2");
check(len4 <= Cfold * 2, "n=4 length <= C log2(n)");
check(len16 <= Cfold * 4, "n=16 length <= C log2(n)");
check(len16 < 4*len4, "n=16 length not Theta(n2) vs n1");

Ca4 = commit(a4); Cb4 = commit(b4);
Cab4 = lift(Mod(g, N)^(evalp(a4, tau)*evalp(b4, tau)));
check(verify(Ps32, Ca4, Cb4, Cab4, pr4, 4) == 1, "honest product n=4 accepts");

Ca16 = commit(a16); Cb16 = commit(b16);
Cab16 = lift(Mod(g, N)^(evalp(a16, tau)*evalp(b16, tau)));
check(verify(Ps32, Ca16, Cb16, Cab16, pr16, 16) == 1, "honest product n=16 accepts");

Csum4 = (Ca4 * Cb4) % N;
check(Csum4 != Cab4, "n=4 sum encoding differs from product");
check(verify(Ps32, Ca4, Cb4, Csum4, pr4, 4) == 0, "group-mul rejected as the product n=4");

\\ QAP: A=1+X, B=2, pad B to length 2.  C=2+2X, H=0, Z=X.
A = [1, 1]; B = padto([2], 2);
CA_q = commit(A); CB_q = commit(B);
CC_q = commit([2, 2]); CHZ_q = commit([0]);
CAB_q = (CC_q * CHZ_q) % N;
prQ = prove(A, B);
check(evalp(A, tau)*evalp(B, tau) - evalp([2, 2], tau) == 0, "QAP identity at tau");
check(CAB_q == lift(Mod(g, N)^(evalp(A, tau)*evalp(B, tau))), "C_C C_HZ is C_AB");
check(verify(Ps32, CA_q, CB_q, CAB_q, prQ, 2) == 1, "honest QAP encodings accept");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
