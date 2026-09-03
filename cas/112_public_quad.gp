\\ Public quadratic check of two committed evaluations.
\\ Mirrors PublicQuad.v.
\\
\\ Setup may use tau and coefficients.  The check itself is
\\ public_quad_check(Ps, CA, CB, CAB, QA, QB, bound): encodings
\\ and public CRS slots only -- no tau, no coefficient lists,
\\ no integer h(tau).
\\ Pin N = pin_N=187, g=3, tau=5, a=[2,3], b=[1,4] from cas/95.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N = pin_N; g = 3; tau = 5;
evalp(cs, x) = {
  my(s = 0, p = 1, ii);
  for(ii = 1, length(cs), s += cs[ii]*p; p *= x);
  s
};
commit(cs) = lift(Mod(g, N)^evalp(cs, tau));
slot(ii, a) = lift(Mod(g, N)^((tau^ii)*a));

\\ --- public check (no tau, no coeff lists) ---
find_exp(P, Q, bound) = {
  my(kk);
  for(kk = 0, bound-1, if(lift(Mod(P, N)^kk) == Q, return(kk)));
  -1
};
recover(Ps, Qs, bound) = {
  my(ii, ks = vector(length(Qs)));
  for(ii = 1, length(Qs), \
    my(kk = find_exp(Ps[ii], Qs[ii], bound)); \
    if(kk < 0, return(-1)); \
    ks[ii] = kk);
  ks
};
gprod(qs) = {
  my(p = 1, ii);
  for(ii = 1, length(qs), p = (p * qs[ii]) % N);
  p
};
quad_combine(Ps, as, bs) = {
  my(acc = 1, ii, jj);
  for(ii = 1, length(as), \
    for(jj = 1, length(bs), \
      my(Pij = Ps[ii + jj - 1]); \
      acc = (acc * lift(Mod(Pij, N)^(as[ii]*bs[jj]))) % N));
  acc
};
public_quad_check(Ps, CA, CB, CAB, QA, QB, bound) = {
  my(as = recover(Ps, QA, bound));
  my(bs = recover(Ps, QB, bound));
  if(type(as) == "t_INT", return(0));
  if(type(bs) == "t_INT", return(0));
  if(gprod(QA) != CA, return(0));
  if(gprod(QB) != CB, return(0));
  if(quad_combine(Ps, as, bs) != CAB, return(0));
  1
};

\\ --- setup: CRS and honest encodings (uses tau; not check inputs) ---
a = [2, 3];
b = [1, 4];
ab = [2, 11, 12];
bound = 5;
nslots = length(a) + length(b);
Ps = vector(nslots);
for(ii = 0, nslots-1, Ps[ii+1] = lift(Mod(g, N)^(tau^ii)));
QA = [slot(0, a[1]), slot(1, a[2])];
QB = [slot(0, b[1]), slot(1, b[2])];
Ca = commit(a); Cb = commit(b); Cab = commit(ab);
Csum = (Ca * Cb) % N;

check(evalp(ab, tau) == evalp(a, tau)*evalp(b, tau), "eval(conv)=eval a * eval b");
check(Csum != Cab, "group product encoding differs from field product");
check(Csum == commit([a[1]+b[1], a[2]+b[2]]), "group product is the sum encoding");

as_rec = recover(Ps, QA, bound);
bs_rec = recover(Ps, QB, bound);
check(type(as_rec) != "t_INT" && as_rec == a, "find_exp recovers a from slots vs P_i");
check(type(bs_rec) != "t_INT" && bs_rec == b, "find_exp recovers b from slots vs P_i");
check(gprod(QA) == Ca, "assemble QA = C_A");
check(gprod(QB) == Cb, "assemble QB = C_B");
check(quad_combine(Ps, a, b) == Cab, "bilinear CRS combine is C_{a*b}");

\\ the check is invoked on encodings / public CRS only
acc_prod = public_quad_check(Ps, Ca, Cb, Cab, QA, QB, bound);
acc_sum  = public_quad_check(Ps, Ca, Cb, Csum, QA, QB, bound);
check(acc_prod == 1, "check accepts honest field-product encodings");
check(acc_sum == 0, "check rejects group-mul as the product");

\\ QAP identity: A=1+X, B=2, C=2+2X, H=0, Z=X.  AB-C = HZ.
A = [1, 1]; B = [2]; C = [2, 2]; H = [0]; Zpoly = [0, 1];
check(evalp(A, tau)*evalp(B, tau) - evalp(C, tau) == evalp(H, tau)*evalp(Zpoly, tau), \
  "QAP identity at tau");
QA_q = [slot(0, A[1]), slot(1, A[2])];
QB_q = [slot(0, B[1])];
CA_q = commit(A); CB_q = commit(B);
CC_q = commit(C); CHZ_q = commit([0]);
CAB_q = (CC_q * CHZ_q) % N;
check(CAB_q == commit([2, 2]), "C_C * C_{HZ} is C_{AB}");
acc_qap = public_quad_check(Ps, CA_q, CB_q, CAB_q, QA_q, QB_q, bound);
check(acc_qap == 1, "check accepts QAP-identity encodings");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
