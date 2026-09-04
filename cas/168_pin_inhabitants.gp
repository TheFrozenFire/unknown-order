\\ Restored inhabitant maps from pin_y / pin_x / pin_e / pin_lam.
\\ The pin-generic rewrite had flattened these names to y^λ ≡ 1.
\\ Campaign objects come from pin.gp; fates are of this pin.
\\ Mirrors SolverShape, SrsaWriteX, SrsaResidual, SrsaDict,
\\ SrsaPeriod, SrsaWriteE, SrsaExtra, FilterShape, ArithShape,
\\ SolverRestrict.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; y=pin_y; x=pin_x; e=pin_e;
d=pin_d; lam=pin_lam; yo=pin_y_ord; g=pin_g;
s1=pin_sqrt1_mixed;

\\ --- residual leftover language ---
check(lift(Mod(y,N)^lam)==1,            "residual_y_to_lambda");
check(lift(Mod(y,N)^yo)==1,             "residual_y_to_ord");
check(znorder(Mod(y,N))==yo,            "period_eq_order_40");
check(lift(Mod(y,N)^(yo/2))!=1,         "period_eq_y20");
check(lift(Mod(y,N)^d)==x,              "residual_x_is_y_to_27");
check(gcd(d, yo)==1,                    "dict_27th_is_inverse_auto gcd");
check((e*d)%lam==1,                     "e d inverse mod lambda");
check(lift(Mod(x,N)^e)==y,              "residual unique cube at leftover");
check(znorder(Mod(x,N))==yo,            "residual_x_order_40");
check(lift(Mod(x,N)^(yo/2))!=1,         "residual_x_order_40_not_20");
check(lift(Mod(x,N)^16)!=1,             "residual_x_not_ord16");
check(lift(Mod(x,N)^10)!=1,             "residual_x_not_ord10");
check(gcd(x-y,N)==1,                    "arith_witness_gap_no_split");
check(gcd(lift(Mod(y,N)^yo)-1,N)==N,    "period_gcd_full_period");

\\ --- public X(N,y) does not invert y ---
check(lift(Mod(N-x,N)^e)!=y,            "xmap_associate");
check(lift(Mod(y,N)^e)!=x,              "xmap_encrypt_as_decrypt");
check(lift(Mod(lift(Mod(y,N)^5),N)^e)!=y, "xmap_odd_monomial_y5");
check(lift(Mod(y,N)^y)!=y,              "xmap_y_to_the_y");
check(lift(Mod(y,N)^(N-1))!=y,          "xmap_y_to_Nminus1");
check(lift(Mod(y,N)^(N+1))!=y,          "xmap_y_to_Nplus1");
check(lift(Mod(y\2,N)^e)!=y,            "xmap_half_y");
check(lift(Mod(y+1,N)^e)!=y,            "xmap_y_plus_1_as_x");
check(lift(Mod(y-1,N)^e)!=y,            "xmap_y_minus_1");
check(lift(Mod(2*y+1,N)^e)!=y,          "xmap_two_y_plus_1");
check(lift(Mod((y*y+1)%N,N)^e)!=y,      "xmap_y2_plus_1");
check(lift(Mod((y*y-1)%N,N)^e)!=y,      "xmap_y2_minus_1");
check(lift(Mod(-1,N)^e)!=y,             "xmap_x_eq_Nminus1");
check(lift(Mod(1,N)^e)==1 && 1!=y,      "xmap_identity_not_root");
check(lift(Mod(pin_phi,N)^e)!=y,        "xmap_x_eq_phi");
check(lift(Mod((256+y)%N,N)^e)!=y,      "xmap_pkcs_pad");
check(gcd(N^2+N+1, lam)==1,             "xmap_phi3_of_N");
check(lift(Mod(lift(Mod(y,N)^9),N)^e)==x && gcd(x-y,N)==1, "xmap_y9_cubes_to_root");

\\ --- solver shapes ---
check(lift(Mod(lift(Mod(y,N)^2),N)^e)!=y, "shape_monomial_k2_pin");
check(lift(Mod(y,N)^d)==x,              "shape_trapdoor_chain_d27");
xq = (1 + y*y) % N;
check(lift(Mod(xq,N)^e)!=y && gcd(lift(Mod(xq,N)^e)-y,N)==1, "shape_poly_x_quadratic");
check(p>1 && p<N && N%p==0,             "shape_crt_moduli_are_factors p");
check(q>1 && q<N && N%q==0,             "shape_crt_moduli_are_factors q");
check(lift(Mod(x,N)^(N-1))!=1,          "shape_public_exp_not_membership");

\\ --- filters ---
check(lift(Mod(y,N)^2)!=lift(Mod(-1,N)), "filter_y_square_not_minus1");
check(kronecker(10,N)==1,               "filter_jacobi_10_plus");
check(lift(Mod(10,N)^e)!=y,             "filter_jacobi_10_plus_not_leftover");
check(lift(Mod(x,N)^e)==y && lift(Mod(10,N)^e)!=y, "filter_x_cube_check_is_rsa_e3");

\\ --- period / annihilator quality ---
check(gcd((lift(Mod(y,N)^2)+1)%N, N)==1, "period_y2_plus_1_gcd");
check(gcd(x*x-1, N)==1,                 "period_x2_minus_1_int");
check(gcd(lift(Mod(x,N)^4)-1, N)==1,    "period_x4_minus_1");
check(gcd(lift(Mod(g,N)^8)-1, N)==1,    "period_three_pow8_no_split");
check(lift(Mod(10,N)^16)==1,            "period_ten_pow16");
check(lift(Mod(5,N)^lam)==1 && lift(Mod(5,N)^(lam/2))!=1, "period_five_max_order");
check(lift(Mod(y,N)^(N-1))!=1 && gcd(lift(Mod(y,N)^(N-1))-1,N)==1, "period_y_Nminus1_no_annihilator");
check(lift(Mod(x,N)^(N-1))!=1,          "period_x_Nminus1_no_membership");

\\ --- dictionary / cubing / SAGM ---
check(N % yo == d,                      "dict_N_mod_40_is_d");
check(lift((Mod(2,N)^d)^e)==2,          "dict_cube_root_of_2");
check(lift((Mod(g,N)^d)^e)==g,          "dict_sagm_of_3");
c1 = lift(Mod(y,N)^e);
c2 = lift(Mod(c1,N)^e);
c3 = lift(Mod(c2,N)^e);
check(c1!=y && c2!=y && c3==x,          "dict cubing orbit y to leftover x");
check(lift(Mod(2,N)^d)!=x,              "SAGM of 2 is not leftover of y");

\\ --- public E(N,y) ---
check(gcd(25,lam)!=1,                   "emap_e25_shares_lambda");
check(gcd(y-1, N-1)==1,                 "emap_gcd_yminus1_Nminus1");
check(gcd(N, lam)==1,                   "emap_e_eq_N coprime");
check((N-1)%lam != 0,                   "emap_e_eq_N not annihilator");
check(gcd(N-2, lam)!=1,                 "emap_e_eq_Nminus2");
check(gcd(y-1, lam)!=1,                 "emap_e_y_minus_1_shares");
check(yo%2==0,                          "emap_ord_y_even");

\\ --- extra tapes ---
check(lift(Mod(2,N)^lam)==1,            "extra_sequential_square_period");
check(lift(Mod(2,N)^(lam+1))==2,        "extra_adaptive_lambda_plus_one");
check(gcd(x-y,N)==1,                    "extra_y_minus_x");
check(N == (N\100)*100 + ((N\10)%10)*10 + (N%10), "extra_digits_of_N");
check(lift(Mod(y,N)^e)!=y,              "extra_related_y_cube");

\\ --- reject-sample public e ---
check(gcd(e, N-1)!=1,                   "public e not coprime to N-1");
check(gcd(5, N-1)==1,                   "next odd 5 is coprime to N-1");
check(gcd(5, lam)!=1,                   "that 5 shares lambda so not residual");

\\ --- order of 2 ---
check(lift(Mod(2,N)^yo)==1,             "residual_ltwo_ord40");
check(lift(Mod(2,N)^(yo/2))!=1,         "residual_ord2_is_40");
check(lift(Mod(g,N)^yo)!=1,             "residual_three_not_in_cyc_y");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
