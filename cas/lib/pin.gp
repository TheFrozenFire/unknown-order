\\ Shared Strong-RSA pin and peel predicates.
\\ Loaded by cas/134_whole_identity.gp (not globbed by run-check).
\\ Pin vector P = [N, y, x, e, lam].

init_pin() = {
  p = 11; q = 17;
  N = p*q;
  y = 36; x = 42; e = 3;
  lam = lcm(p-1, q-1);
  Pin = [N, y, x, e, lam];
};

residual() = {
  gcd(y,N)==1
  && lift(Mod(x,N)^e)==y
  && e>1
  && e%2==1
  && gcd(e,lam)==1
  && (e-1)%lam != 0
  && gcd(x,N)==1
};

factor_from_x() = {
  my(g = gcd(x, N));
  g>1 && g<N
};

peel_nonunit() = lift(Mod(11,N)^3)==22 && gcd(11,N)==11;
peel_units() = gcd(42,N)==1 && gcd(36,N)==1 && lift(Mod(42,N)^3)==36;
peel_jacobi() = kronecker(2,N)==-1 && kronecker(36,N)==1;
peel_even() = lift(Mod(6,N)^2)==36 && lift(Mod(181,N)^2)==36;
peel_mixed() = lift(Mod(28,N)^2)==36 && gcd(28-6,N)==11;
peel_miller() = lift(Mod(67,N)^2)==1 && gcd(67-1,N)==11;
peel_all() = {
  peel_nonunit() && peel_units() && peel_jacobi()
  && peel_even() && peel_mixed() && peel_miller()
};

\\ Named extra pins (in-corpus second moduli).  Vectors do not mutate
\\ the default Pin globals.  Full residual pair when one is named;
\\ otherwise [N, lam] (or [N^2] for the Paillier carrier).

\\ Safeprime-shaped residual (SolverRestrict): 2^7 \equiv 51 (mod 77).
extra_77() = [7*11, 51, 2, 7, lcm(6,10)];
extra_77_residual() = {
  my(P=extra_77(), Ns=P[1], ys=P[2], xs=P[3], es=P[4], lams=P[5]);
  gcd(ys,Ns)==1
  && lift(Mod(xs,Ns)^es)==ys
  && es>1 && es%2==1
  && gcd(es,lams)==1
  && (es-1)%lams != 0
  && gcd(xs,Ns)==1
};

\\ Williams pair p=11 \equiv 3 (mod 8), q=23 \equiv 7 (mod 8).
extra_253() = [11*23, lcm(10,22)];
extra_253_ok() = {
  extra_253()[1]==253 && extra_253()[2]==110
  && 11%8==3 && 23%8==7
};

\\ Takagi / Okamoto-Uchiyama p^2 q.
extra_45() = [3^2*5, lcm(6,4)];
extra_45_ok() = {
  extra_45()[1]==45 && extra_45()[2]==12
  && lift(Mod(1+3,9)^2)==(1+2*3)%9
};

\\ Triprime.
extra_105() = [3*5*7, lcm(lcm(2,4),6)];
extra_105_ok() = {
  extra_105()[1]==105 && extra_105()[2]==12
  && gcd(3, extra_105()[2])==3
};

\\ Coprime second modulus, same y.
extra_247() = [13*19, lcm(12,18)];
extra_247_ok() = {
  extra_247()[1]==247 && extra_247()[2]==36
  && gcd(11*17, extra_247()[1])==1 && 36%247==36
};

\\ Paillier carrier N^2 of the default pin.
extra_Nsq() = [(11*17)^2];
extra_Nsq_ok() = {
  extra_Nsq()[1]==34969
  && lift(Mod(1+11*17, extra_Nsq()[1])^1)==1+11*17
};

\\ Computed sieve witnesses on the default pin (twin of rocq/Pin.v).
\\ Loaded with this file; SieveRelation.v consumes the same names.
pin_dixon_a = 24;
pin_dixon_b = 37;
pin_dixon_r = 15;
pin_dixon_s = 60;
pin_dixon_t = 30;
pin_dixon_b2 = 38;
pin_dixon_s2 = 135;
pin_dixon_t2 = 45;
pin_asquare_a = 14;
pin_asquare_t = 3;
pin_nfs_irr_c0 = 5; pin_nfs_irr_c1 = 1; pin_nfs_irr_c2 = 1; pin_nfs_irr_m = 13;
pin_nfs_red_c0 = 7; pin_nfs_red_c1 = 8; pin_nfs_red_c2 = 1; pin_nfs_red_m = 10;
pin_ts_a1 = -15; pin_ts_b1 = 1; pin_ts_a2 = -6; pin_ts_b2 = 1;
pin_ts_T = 20; pin_ts_U = 6; pin_ts_y = 1;
pin_os_a = 1; pin_os_b = 1; pin_os_gs = 3; pin_os_fs = 4;
