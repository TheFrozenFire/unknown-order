\\ Shared Strong-RSA pin — twin of rocq/Pin.v.
\\ Frozen pins (pin187_*, pin1363_*, pin2491_*) are never rewritten
\\ by swap_pin.py.  pin_* is the campaign alias (BEGIN/END block).

pin187_p = 11; pin187_q = 17;
pin187_N = pin187_p*pin187_q;
pin187_e = 3; pin187_d = 27;
pin187_y = 36; pin187_x = 42;
pin187_lam = 80; pin187_phi = 160;
pin187_g = 3; pin187_g_ord_p = 5; pin187_g_ord_q = 16;
pin187_y_ord = 40; pin187_y_ord_p = 5; pin187_y_ord_q = 8; pin187_x_k = 5;
pin187_inv3_p = 7; pin187_inv3_q = 11;
pin187_root_ca = 34; pin187_root_cb = 154;
pin187_ord2_p = 10; pin187_ord2_q = 8;
pin187_sqrt1_mixed = 67; pin187_sqrt1_mixed2 = 120;
pin187_dixon_a = 24; pin187_dixon_b = 37;
pin187_dixon_r = 15; pin187_dixon_s = 60; pin187_dixon_t = 30;
pin187_dixon_b2 = 38; pin187_dixon_s2 = 135; pin187_dixon_t2 = 45;
pin187_asquare_a = 14; pin187_asquare_t = 3;
pin187_nfs_irr_c0 = 5; pin187_nfs_irr_c1 = 1; pin187_nfs_irr_c2 = 1; pin187_nfs_irr_m = 13;
pin187_nfs_red_c0 = 7; pin187_nfs_red_c1 = 8; pin187_nfs_red_c2 = 1; pin187_nfs_red_m = 10;
pin187_ts_a1 = -15; pin187_ts_b1 = 1; pin187_ts_a2 = -6; pin187_ts_b2 = 1; pin187_ts_T = 20; pin187_ts_U = 6; pin187_ts_y = 1;
pin187_os_a = 1; pin187_os_b = 1; pin187_os_gs = 3; pin187_os_fs = 4;

pin1363_p = 29; pin1363_q = 47;
pin1363_N = pin1363_p*pin1363_q;
pin1363_e = 3; pin1363_d = 215;
pin1363_y = 486; pin1363_x = 42;
pin1363_lam = 644; pin1363_phi = 1288;
pin1363_g = 3; pin1363_g_ord_p = 28; pin1363_g_ord_q = 23;
pin1363_y_ord = 322; pin1363_y_ord_p = 14; pin1363_y_ord_q = 23; pin1363_x_k = 14;
pin1363_inv3_p = 19; pin1363_inv3_q = 31;
pin1363_root_ca = 987; pin1363_root_cb = 377;
pin1363_ord2_p = 28; pin1363_ord2_q = 23;
pin1363_sqrt1_mixed = 610; pin1363_sqrt1_mixed2 = 753;
pin1363_dixon_a = 37; pin1363_dixon_b = 43;
pin1363_dixon_r = 6; pin1363_dixon_s = 486; pin1363_dixon_t = 54;
pin1363_dixon_b2 = 43; pin1363_dixon_s2 = 486; pin1363_dixon_t2 = 54;
pin1363_asquare_a = 38; pin1363_asquare_t = 9;
pin1363_nfs_irr_c0 = 31; pin1363_nfs_irr_c1 = 1; pin1363_nfs_irr_c2 = 1; pin1363_nfs_irr_m = 36;
pin1363_nfs_red_c0 = -17; pin1363_nfs_red_c1 = 16; pin1363_nfs_red_c2 = 1; pin1363_nfs_red_m = 30;
pin1363_ts_a1 = 1; pin1363_ts_b1 = 0; pin1363_ts_a2 = 1; pin1363_ts_b2 = 0; pin1363_ts_T = 1; pin1363_ts_U = 1; pin1363_ts_y = 1;
pin1363_os_a = 1; pin1363_os_b = 1; pin1363_os_gs = 3; pin1363_os_fs = 4;

pin2491_p = 47; pin2491_q = 53;
pin2491_N = pin2491_p*pin2491_q;
pin2491_e = 3; pin2491_d = 399;
pin2491_y = 1849; pin2491_x = 42;
pin2491_lam = 1196; pin2491_phi = 2392;
pin2491_g = 3; pin2491_g_ord_p = 23; pin2491_g_ord_q = 52;
pin2491_y_ord = 299; pin2491_y_ord_p = 23; pin2491_y_ord_q = 13; pin2491_x_k = 23;
pin2491_inv3_p = 31; pin2491_inv3_q = 35;
pin2491_root_ca = 424; pin2491_root_cb = 2068;
pin2491_ord2_p = 23; pin2491_ord2_q = 52;
pin2491_sqrt1_mixed = 847; pin2491_sqrt1_mixed2 = 1644;
pin2491_dixon_a = 51; pin2491_dixon_b = 59;
pin2491_dixon_r = 110; pin2491_dixon_s = 990; pin2491_dixon_t = 330;
pin2491_dixon_b2 = 59; pin2491_dixon_s2 = 990; pin2491_dixon_t2 = 330;
pin2491_asquare_a = 50; pin2491_asquare_t = 3;
pin2491_nfs_irr_c0 = 41; pin2491_nfs_irr_c1 = 1; pin2491_nfs_irr_c2 = 1; pin2491_nfs_irr_m = 49;
pin2491_nfs_red_c0 = -5; pin2491_nfs_red_c1 = 4; pin2491_nfs_red_c2 = 1; pin2491_nfs_red_m = 48;
pin2491_ts_a1 = 1; pin2491_ts_b1 = 0; pin2491_ts_a2 = 1; pin2491_ts_b2 = 0; pin2491_ts_T = 1; pin2491_ts_U = 1; pin2491_ts_y = 1;
pin2491_os_a = 1; pin2491_os_b = 1; pin2491_os_gs = 3; pin2491_os_fs = 4;

\\ CAMPAIGN_ALIAS_BEGIN pin187
pin_p = pin187_p;
pin_q = pin187_q;
pin_N = pin187_N;
pin_e = pin187_e;
pin_d = pin187_d;
pin_y = pin187_y;
pin_x = pin187_x;
pin_lam = pin187_lam;
pin_phi = pin187_phi;
pin_g = pin187_g;
pin_g_ord_p = pin187_g_ord_p;
pin_g_ord_q = pin187_g_ord_q;
pin_y_ord = pin187_y_ord;
pin_y_ord_p = pin187_y_ord_p;
pin_y_ord_q = pin187_y_ord_q;
pin_x_k = pin187_x_k;
pin_inv3_p = pin187_inv3_p;
pin_inv3_q = pin187_inv3_q;
pin_ord2_p = pin187_ord2_p;
pin_ord2_q = pin187_ord2_q;
pin_root_ca = pin187_root_ca;
pin_root_cb = pin187_root_cb;
pin_sqrt1_mixed = pin187_sqrt1_mixed;
pin_sqrt1_mixed2 = pin187_sqrt1_mixed2;
pin_dixon_a = pin187_dixon_a;
pin_dixon_b = pin187_dixon_b;
pin_dixon_r = pin187_dixon_r;
pin_dixon_s = pin187_dixon_s;
pin_dixon_t = pin187_dixon_t;
pin_dixon_b2 = pin187_dixon_b2;
pin_dixon_s2 = pin187_dixon_s2;
pin_dixon_t2 = pin187_dixon_t2;
pin_asquare_a = pin187_asquare_a;
pin_asquare_t = pin187_asquare_t;
pin_nfs_irr_c0 = pin187_nfs_irr_c0;
pin_nfs_irr_c1 = pin187_nfs_irr_c1;
pin_nfs_irr_c2 = pin187_nfs_irr_c2;
pin_nfs_irr_m = pin187_nfs_irr_m;
pin_nfs_red_c0 = pin187_nfs_red_c0;
pin_nfs_red_c1 = pin187_nfs_red_c1;
pin_nfs_red_c2 = pin187_nfs_red_c2;
pin_nfs_red_m = pin187_nfs_red_m;
pin_ts_a1 = pin187_ts_a1;
pin_ts_b1 = pin187_ts_b1;
pin_ts_a2 = pin187_ts_a2;
pin_ts_b2 = pin187_ts_b2;
pin_ts_T = pin187_ts_T;
pin_ts_U = pin187_ts_U;
pin_ts_y = pin187_ts_y;
pin_os_a = pin187_os_a;
pin_os_b = pin187_os_b;
pin_os_gs = pin187_os_gs;
pin_os_fs = pin187_os_fs;
\\ CAMPAIGN_ALIAS_END
pin_Nsq = pin_N^2;

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

peel_nonunit() = lift(Mod(pin187_p,pin187_N)^3)==22 && gcd(pin187_p,pin187_N)==pin187_p;
peel_units() = gcd(pin187_x,pin187_N)==1 && gcd(pin187_y,pin187_N)==1 && lift(Mod(pin187_x,pin187_N)^pin187_e)==pin187_y;
peel_jacobi() = kronecker(2,pin187_N)==-1 && kronecker(pin187_y,pin187_N)==1;
peel_even() = lift(Mod(6,pin187_N)^2)==pin187_y && lift(Mod(181,pin187_N)^2)==pin187_y;
peel_mixed() = lift(Mod(28,pin187_N)^2)==pin187_y && gcd(28-6,pin187_N)==pin187_p;
peel_miller() = lift(Mod(pin187_sqrt1_mixed,pin187_N)^2)==1 && gcd(pin187_sqrt1_mixed-1,pin187_N)==pin187_p;
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
