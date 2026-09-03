\\ Shared Strong-RSA pin — twin of rocq/Pin.v.
\\ File-level names so consumers can read this without clobbering
\\ local p/q/N until they call init_pin().

pin_p = 11; pin_q = 17;
pin_N = pin_p*pin_q;
pin_e = 3; pin_d = 27;
pin_y = 36; pin_x = 42;
pin_lam = 80; pin_phi = 160;
pin_g = 3; pin_g_ord_p = 5; pin_g_ord_q = 16;
pin_y_ord = 40; pin_y_ord_p = 5; pin_y_ord_q = 8; pin_x_k = 5;
pin_inv3_p = 7; pin_inv3_q = 11;
pin_ord2_p = 10; pin_ord2_q = 8;
pin_sqrt1_mixed = 67; pin_sqrt1_mixed2 = 120;

pin_77_p = 7; pin_77_q = 11; pin_77 = pin_77_p*pin_77_q;
pin_77_lam = 30; pin_77_y = 51; pin_77_x = 2; pin_77_e = 7;
pin_91_p = 13; pin_91_q = 7; pin_91 = pin_91_p*pin_91_q;
pin_91_lam = 12; pin_91_om_p = 3; pin_91_om_q = 2;
pin_91_gp = 29; pin_91_gq = 79; pin_91_diag = 16;
pin_247_p = 13; pin_247_q = 19; pin_247 = pin_247_p*pin_247_q;
pin_247_lam = 36; pin_247_y = 69; pin_247_x = 179; pin_247_e = 5;
pin_247_noncube = 7;
pin_253_p = 11; pin_253_q = 23; pin_253 = pin_253_p*pin_253_q; pin_253_lam = 110;
pin_45_p = 3; pin_45_q = 5; pin_45 = pin_45_p^2*pin_45_q; pin_45_lam = 12;
pin_105_p = 3; pin_105_q = 5; pin_105_r = 7;
pin_105 = pin_105_p*pin_105_q*pin_105_r; pin_105_lam = 12;
pin_Nsq = pin_N^2;

init_pin() = {
  p = pin_p; q = pin_q;
  N = pin_N;
  y = pin_y; x = pin_x; e = pin_e;
  lam = pin_lam;
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
extra_77() = [pin_77, pin_77_y, pin_77_x, pin_77_e, pin_77_lam];
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
extra_253() = [pin_253, pin_253_lam];
extra_253_ok() = {
  extra_253()[1]==pin_253 && extra_253()[2]==pin_253_lam
  && pin_253_p%8==3 && pin_253_q%8==7
};

\\ Takagi / Okamoto-Uchiyama p^2 q.
extra_45() = [pin_45, pin_45_lam];
extra_45_ok() = {
  extra_45()[1]==pin_45 && extra_45()[2]==pin_45_lam
  && lift(Mod(1+pin_45_p, pin_45_p^2)^2)==(1+2*pin_45_p)%(pin_45_p^2)
};

\\ Triprime.
extra_105() = [pin_105, pin_105_lam];
extra_105_ok() = {
  extra_105()[1]==pin_105 && extra_105()[2]==pin_105_lam
  && gcd(3, extra_105()[2])==3
};

\\ Coprime second modulus, same y.
extra_247() = [pin_247, pin_247_lam];
extra_247_ok() = {
  extra_247()[1]==pin_247 && extra_247()[2]==pin_247_lam
  && gcd(pin_N, extra_247()[1])==1 && pin_y%pin_247==pin_y
};

\\ Paillier carrier N^2 of the default pin.
extra_Nsq() = [pin_Nsq];
extra_Nsq_ok() = {
  extra_Nsq()[1]==pin_Nsq
  && lift(Mod(1+pin_N, extra_Nsq()[1])^1)==1+pin_N
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
