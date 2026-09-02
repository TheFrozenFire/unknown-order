\\ Verbose CAS dump of the joined Strong-RSA identity.
\\ Not numbered, not globbed by run-check.  Prints live PARI residues
\\ as KEY k=v records.  Probe names and values avoid the word "fail".
\\
\\ Format cas-verbose/v1 — one record per line:
\\   KIND field=value field=value ...
\\ KIND is META | PIN | DERIVED | RESIDUAL | PEEL | CL | EXTRA | WHOLE.
\\ Integers are lift(Mod(...)) or gcd/znorder computed in this session.
\\ fate= is the catalog fate of the class, not inferred from a gcd.

read("lib/pin.gp");
read("lib/classes.gp");
init_pin();

emit(kind, rest) = printf("%s %s\n", kind, rest);

powm(a, ee) = lift(Mod(a, N)^ee);
gN(a) = gcd(a, N);
gNy(out) = gcd(out - y, N);

emit("META", "format=cas-verbose/v1 object=joined_identity");

emit("PIN", Str("N=", N, " p=", p, " q=", q, " y=", y, " x=", x, " e=", e, " lam=", lam, " phi=", eulerphi(N), " d=", lift(1/Mod(e,lam))));

ordy = znorder(Mod(y, N));
ord2 = znorder(Mod(2, N));
ord3 = znorder(Mod(3, N));
yinv = lift(1/Mod(y, N));
xinv = lift(1/Mod(x, N));
y3 = powm(y, 3);
y5 = powm(y, 5);
emit("DERIVED", Str("ord_y=", ordy, " ord_2=", ord2, " ord_3=", ord3, " y_inv=", yinv, " x_inv=", xinv, " y^3=", y3, " y^5=", y5, " N_half=", N\2, " N-x=", N-x, " sqrt_y=", sqrtint(y), " x-y=", x-y, " N_mod_ord_y=", N%ordy, " jacobi_y=", kronecker(y,N), " jacobi_2=", kronecker(2,N), " y_plus_sqrt=", y+sqrtint(y)));

emit("RESIDUAL", Str("x^e=", powm(x,e), " want=", y, " hit=", powm(x,e)==y, " gcd_x=", gN(x), " gcd_y=", gN(y), " e_odd=", e%2==1, " gcd_e_lam=", gcd(e,lam), " lam_div_e-1=", (e-1)%lam==0, " factor_from_x=", factor_from_x()));

emit("PEEL", Str("kind=nonunit x=11 e=3 yhat=", powm(11,3), " gcd=", gN(11), " splits=", gN(11)>1 && gN(11)<N));
emit("PEEL", Str("kind=units x=42 y=36 x^3=", powm(42,3), " gcd_x=", gN(42), " gcd_y=", gN(36)));
emit("PEEL", Str("kind=jacobi (2/N)=", kronecker(2,N), " (36/N)=", kronecker(36,N)));
emit("PEEL", Str("kind=even x=6 x2=", powm(6,2), " assoc=", powm(181,2), " e=2"));
emit("PEEL", Str("kind=mixed x=28 x2=", powm(28,2), " gcd(28-6)=", gcd(28-6,N)));
emit("PEEL", Str("kind=miller g=67 g^2=", powm(67,2), " gcd(g-1)=", gcd(67-1,N)));

\\ ----- CL 1-12 x=f(y) / e=f(y) / extras of A -----
emit("CL", Str("n=01 family=x_of_y map=y^3 fate=split_onesided x=", y3, " x^3=", powm(y3,3), " want=", y, " hit=", powm(y3,e)==y, " split_gcd=", gNy(powm(y3,e))));
emit("CL", Str("n=02 family=x_of_y map=N-x fate=miss x=", N-x, " x^3=", powm(N-x,3), " want=", y, " hit=", powm(N-x,e)==y, " split_gcd=", gNy(powm(N-x,e))));
emit("CL", Str("n=03 family=x_of_y map=midpoint fate=miss N_half=", N\2, " mid=", abs(y-N\2), " mid^3=", powm(abs(y-N\2),3), " hit=", powm(abs(y-N\2),e)==y));
emit("CL", Str("n=04 family=e_of_y map=phi(y) fate=peel_even e=", eulerphi(y), " e_odd=", eulerphi(y)%2==1, " gcd_e_lam=", gcd(eulerphi(y),lam)));
emit("CL", Str("n=05 family=e_of_y map=hamming(y) fate=peel_even e=", hammingweight(y), " e_odd=", hammingweight(y)%2==1));
emit("CL", Str("n=06 family=query map=shamir_two_leftovers fate=product_not_factor x1=42 e1=3 x2=60 e2=7 gcd_e=", gcd(3,7), " gcd(x1-x2)=", gcd(42-60,N)));
emit("CL", Str("n=07 family=modulus map=paillier_N^2 fate=different_group N2=", N^2, " (1+N)^1=", lift(Mod(1+N,N^2)^1)));
V2=62*62-2; V3=62*V2-62;
emit("CL", Str("n=08 family=x_of_y map=lucas_V3 fate=torus P=62 V3=", V3, " V3_mod_N=", V3%N, " want=", y, " hit=", (V3%N)==y));
emit("CL", Str("n=09 family=e_of_y map=lsb(y) fate=peel_even lsb=", y%2));
emit("CL", Str("n=10 family=x_of_y map=y^e fate=miss x=", y3, " want_x=", x, " hit_decrypt=", y3==x));
emit("CL", Str("n=11 family=e_of_y map=e=25 fate=shares_lambda e=25 gcd_e_lam=", gcd(25,lam), " e_odd=1"));
emit("CL", Str("n=12 family=x_of_y map=coppersmith_small fate=leftover bound=N^(1/9) 2^9=", 2^9, " x=", x, " x_lt_bound=", x < 2^9 && 2^9<=N));

\\ ----- 13-32 -----
emit("CL", Str("n=13 family=x_of_y map=y^5 fate=miss x=", y5, " x^3=", powm(y5,3), " hit=", powm(y5,e)==y, " split_gcd=", gNy(powm(y5,e))));
emit("CL", Str("n=14 family=x_of_y map=y^y fate=miss x=", powm(y,y), " hit=", powm(powm(y,y),e)==y, " split_gcd=", gNy(powm(powm(y,y),e))));
emit("CL", Str("n=15 family=x_of_y map=y^N fate=leftover x=", powm(y,N), " hit=", powm(y,N)==x, " N_mod_ord_y=", N%ordy, " d=", lift(1/Mod(e,lam))));
emit("CL", Str("n=16 family=x_of_y map=y^(N-1) fate=miss x=", powm(y,N-1), " hit=", powm(y,N-1)==x, " split_gcd=", gNy(powm(powm(y,N-1),e))));
emit("CL", Str("n=17 family=x_of_y map=y^(N+1) fate=miss x=", powm(y,N+1), " hit=", powm(y,N+1)==x));
emit("CL", Str("n=18 family=x_of_y map=floor_sqrt_y fate=peel_even x=", sqrtint(y), " x^2=", sqrtint(y)^2, " e=2"));
emit("CL", Str("n=19 family=x_of_y map=y/2 fate=miss x=", y\2, " x^3=", powm(y\2,3), " hit=", powm(y\2,e)==y));
br36=fromdigits(Vecrev(binary(36)),2); br43=fromdigits(Vecrev(binary(43)),2);
emit("CL", Str("n=20 family=x_of_y map=bitrev6 fate=split_onesided x=", br36, " x^3=", powm(br36,3), " bitrev43=", br43, " hit=", powm(br36,e)==y, " split_gcd=", gNy(powm(br36,3))));
tri=(36*35/2)%N;
emit("CL", Str("n=21 family=x_of_y map=triangular fate=extra x=", tri, " x^5=", powm(tri,5), " x^3=", powm(tri,3)));
emit("CL", Str("n=22 family=x_of_y map=nextprime(y) fate=miss x=37 x^3=", powm(37,3), " hit=", powm(37,e)==y));
F36=fibonacci(36)%N;
emit("CL", Str("n=23 family=x_of_y map=fibonacci_y fate=split_nonunit x=", F36, " gcd_x=", gN(F36), " x^3=", powm(F36,3), " hit=", powm(F36,e)==y));
emit("CL", Str("n=24 family=x_of_y map=2^y fate=split_onesided x=", powm(2,y), " x^3=", powm(powm(2,y),3), " split_gcd=", gNy(powm(powm(2,y),3))));
emit("CL", Str("n=25 family=x_of_y map=3^y fate=miss x=", powm(3,y), " x^3=", powm(powm(3,y),3)));
phi3y=(y^2+y+1)%N;
emit("CL", Str("n=26 family=x_of_y map=Phi_3(y) fate=miss x=", phi3y, " x^3=", powm(phi3y,3)));
emit("CL", Str("n=27 family=x_of_y map=(y_inv)^3 fate=split_onesided x=", powm(yinv,3), " x^3=", powm(powm(yinv,3),3), " split_gcd=", gNy(powm(powm(yinv,3),3))));
emit("CL", Str("n=28 family=x_of_y map=(y^3)_inv fate=split_onesided x=", lift(1/Mod(y3,N)), " x^3=", powm(lift(1/Mod(y3,N)),3), " split_gcd=", gNy(powm(lift(1/Mod(y3,N)),3))));
hcrt=lift(chinese(Mod(1,11), Mod(36,17)));
emit("CL", Str("n=29 family=x_of_y map=CRT(1,y_mod_q) fate=miss x=", hcrt, " gcd=", gN(hcrt), " x^3=", powm(hcrt,3), " hit=", powm(hcrt,e)==y));
mcrt=lift(chinese(Mod(9,11), Mod(1,17)));
emit("CL", Str("n=30 family=x_of_y map=CRT(9,1) fate=split x=", mcrt, " x^3=", powm(mcrt,3), " split_gcd=", gNy(powm(mcrt,3))));
emit("CL", Str("n=31 family=x_of_y map=integer_JNT fate=miss_unless_cube y+c=", y+28, " 4^3=", 4^3, " c=28"));
emit("CL", Str("n=32 family=x_of_y map=y^2+1 fate=miss x=", (y^2+1)%N, " x^3=", powm((y^2+1)%N,3)));

\\ ----- 33-50 e=f(y) -----
emit("CL", Str("n=33 family=e_of_y map=lambda(y) fate=peel_even e=", lcm(2,6), " e_odd=0"));
emit("CL", Str("n=34 family=e_of_y map=bitlength(y) fate=peel_even e=", 1+logint(y,2)));
emit("CL", Str("n=35 family=e_of_y map=tau(y) fate=leftover_shaped e=", numdiv(y), " gcd_e_lam=", gcd(numdiv(y),lam)));
emit("CL", Str("n=36 family=e_of_y map=sigma(y) fate=leftover e=", sigma(y), " gcd_e_lam=", gcd(sigma(y),lam), " x=25 x^e=", powm(25,sigma(y)), " hit=", powm(25,sigma(y))==y));
emit("CL", Str("n=37 family=e_of_y map=rad(y) fate=peel_even e=6"));
emit("CL", Str("n=38 family=e_of_y map=omega(y) fate=peel_even e=", omega(y)));
emit("CL", Str("n=39 family=e_of_y map=Omega(y) fate=peel_even e=", bigomega(y)));
emit("CL", Str("n=40 family=e_of_y map=lpf(y) fate=leftover e=3 x=42 x^e=", powm(42,3), " hit=1"));
emit("CL", Str("n=41 family=e_of_y map=y+1 fate=leftover_shaped e=", y+1, " nextprime=", nextprime(y), " coincide=", (y+1)==nextprime(y), " gcd_e_lam=", gcd(y+1,lam)));
emit("CL", Str("n=42 family=e_of_y map=odd_part(y) fate=leftover_shaped e=", y/4, " gcd_e_lam=", gcd(y/4,lam)));
emit("CL", Str("n=43 family=e_of_y map=2*ham+1 fate=shares_lambda e=", 2*hammingweight(y)+1, " gcd_e_lam=", gcd(2*hammingweight(y)+1,lam)));
emit("CL", Str("n=44 family=e_of_y map=gcd(y-1,N-1) fate=fallback e=", gcd(y-1,N-1)));
emit("CL", Str("n=45 family=e_of_y map=Phi_3(y)_as_e fate=leftover_shaped e=", y^2+y+1, " e_mod=", (y^2+y+1)%N, " gcd_e_lam=", gcd(y^2+y+1,lam)));
emit("CL", Str("n=46 family=e_of_y map=2*v2(y)+1 fate=shares_lambda v2_ym1=", valuation(y-1,2), " e=", 2*valuation(y,2)+1, " gcd_e_lam=", gcd(2*valuation(y,2)+1,lam)));
emit("CL", Str("n=47 family=e_of_y map=mersenne63 fate=leftover e=63 gcd_e_lam=", gcd(63,lam), " x=9 x^e=", powm(9,63), " hit=", powm(9,63)==y));
emit("CL", Str("n=48 family=e_of_y map=N_mod_y fate=leftover e=", N%y, " gcd_e_lam=", gcd(N%y,lam), " x=60 x^e=", powm(60,N%y), " hit=", powm(60,N%y)==y));
emit("CL", Str("n=49 family=e_of_y map=fermatish_33 fate=leftover e=33 gcd_e_lam=", gcd(33,lam), " x=53 x^e=", powm(53,33), " hit=", powm(53,33)==y));
emit("CL", Str("n=50 family=e_of_y map=smooth_30 fate=peel_even e=30"));

\\ ----- 51-74 extras / queries -----
emit("CL", Str("n=51 family=extra map=d_p fate=one_sided (e*d-1) mod (p-1)=", (e*27-1)%(p-1)));
emit("CL", Str("n=52 family=extra map=p-q fate=split p-q=", p-q, " (p-q)^2=", (p-q)^2, " 4N=", 4*N, " 28^2-4N=", 28^2-4*N));
emit("CL", Str("n=53 family=extra map=sqrt_y fate=split sqrt=6 mixed=28 gcd(28-6)=", gcd(28-6,N)));
emit("CL", Str("n=54 family=extra map=ord(3) fate=trapdoor ord_3=", ord3, " lam=", lam, " equal=", ord3==lam));
emit("CL", Str("n=55 family=extra map=factor(e-1) fate=split e-1=10 factor=", factor(10)));
emit("CL", Str("n=56 family=extra map=factor(N-1) fate=public N-1=", N-1, " factor=", factor(N-1)));
emit("CL", Str("n=57 family=extra map=wiener_d fate=not_small d=27 N^(1/4)~", sqrtint(sqrtint(N))));
emit("CL", Str("n=58 family=extra map=2^lam fate=period 2^lam=", powm(2,lam)));
emit("CL", Str("n=59 family=extra map=v2_heights fate=mismatch v2_ord_p=", valuation(znorder(Mod(2,p)),2), " v2_ord_q=", valuation(znorder(Mod(2,q)),2)));
emit("CL", Str("n=60 family=extra map=primroot_p fate=trapdoor_side primroot_11=", znprimroot(11)));
emit("CL", Str("n=61 family=extra map=half_bits fate=extra hi=", x>>3, " lo=", x%8));
emit("CL", Str("n=62 family=extra map=jacobi_y fate=vacuous (y/N)=", kronecker(y,N)));
emit("CL", Str("n=63 family=query map=y_and_y_inv fate=leftover y_inv=", yinv, " x_inv=", xinv, " x_inv^3=", powm(xinv,3)));
emit("CL", Str("n=64 family=query map=-y fate=miss neg_y=", (-y)%N, " (-y)^3=", powm((-y)%N,3)));
emit("CL", Str("n=65 family=query map=2y fate=extra 2y=", 2*y));
emit("CL", Str("n=66 family=query map=gcd(e,e+2) fate=shamir gcd(3,5)=", gcd(3,5)));
emit("CL", Str("n=67 family=query map=y+1_root fate=miss y+1=", y+1, " 126^3=", powm(126,3)));
emit("CL", Str("n=68 family=query map=batch_gcd_roots fate=no_split gcd(42-60)=", gcd(42-60,N)));
emit("CL", Str("n=69 family=query map=lam+1 fate=search_extra e=", lam+1, " 2^(lam+1)=", powm(2,lam+1)));
emit("CL", Str("n=70 family=query map=two_moduli fate=no_split N2=247 gcd(N,247)=", gcd(N,247), " y_mod_247=", y%247));
emit("CL", Str("n=71 family=query map=twin_exponents fate=shamir gcd(3,5)=", gcd(3,5)));
prodlef=(42*60)%N;
emit("CL", Str("n=72 family=query map=product_leftovers fate=miss prod=", prodlef, " prod^3=", powm(prodlef,3), " hit=", powm(prodlef,e)==y));
emit("CL", Str("n=73 family=query map=rerand_fixed_e fate=leftover e=", e));
emit("CL", Str("n=74 family=query map=coins_independent fate=leftover e=", e, " residual=", residual()));

\\ ----- 75-84 engines -----
emit("CL", Str("n=75 family=engine map=pollard_p-1 fate=split M=60 gcd(2^M-1)=", gcd(powm(2,60)-1,N), " 10|M=", 60%10==0, " 16|M=", 60%16==0));
emit("CL", Str("n=76 family=engine map=rho fate=split tortoise=26 hare=180 gcd=", gcd(26-180,N), " f=x^2+1 walk=2,5,26"));
emit("CL", Str("n=77 family=engine map=bsgs_N-1 fate=wrong_order lam=", lam, " N-1=", N-1, " equal=", lam==N-1));
emit("CL", Str("n=78 family=engine map=fermat fate=split a=14 a^2-N=", 14^2-N, " b=3 p=", 14-3, " q=", 14+3));
emit("CL", Str("n=79 family=engine map=trial fate=split 11|N=", N%11==0));
Vnm2=2; Vnm1=5;
for(n=2,12, V=5*Vnm1-Vnm2; Vnm2=Vnm1; Vnm1=V);
emit("CL", Str("n=80 family=engine map=williams_p+1 fate=split P=5 n=12 V=", Vnm1, " gcd(V-2)=", gcd(Vnm1-2,N)));
emit("CL", Str("n=81 family=engine map=index_N-1 fate=no_split gcd(2^(N-1)-1)=", gcd(powm(2,N-1)-1,N)));
emit("CL", Str("n=82 family=engine map=squaring_only fate=extra 2^8=", powm(2,8)));
emit("CL", Str("n=83 family=engine map=advice_lsb fate=peel_even lsb=", y%2));
emit("CL", Str("n=84 family=engine map=stream_first_bit fate=peel_even bit0=", y%2));

\\ ----- 85-100 modulus / public N / DL -----
emit("CL", Str("n=85 family=modulus map=OU_p2q fate=different_group N45=45 (1+p)^2_mod_p2=", lift(Mod(1+3,9)^2)));
emit("CL", Str("n=86 family=modulus map=DJ_N3 fate=different_group N3=", N^3));
emit("CL", Str("n=87 family=modulus map=cocks_jacobi fate=vacuous (y/N)=", kronecker(y,N)));
emit("CL", Str("n=88 family=modulus map=prime_power_17^2 fate=field 2^11_mod_17=", lift(Mod(2,17)^11)));
emit("CL", Str("n=89 family=modulus map=two_safeprimes fate=shares_lambda N=161 lam=66 gcd(3,66)=", gcd(3,66)));
emit("CL", Str("n=90 family=modulus map=RW_shape fate=shape p11_mod8=", 11%8, " q23_mod8=", 23%8));
emit("CL", Str("n=91 family=modulus map=twins fate=fermat_center 101+103=", 101+103, " center=", (101+103)/2));
emit("CL", Str("n=92 family=modulus map=unbalanced fate=split N=1111 11|N=", 1111%11==0));
emit("CL", Str("n=93 family=modulus map=triprime_105 fate=not_residual lam=12 gcd(3,12)=", gcd(3,12)));
emit("CL", Str("n=94 family=modulus map=prime_17 fate=field 2^11_mod_17=", lift(Mod(2,17)^11), " gcd(3,16)=", gcd(3,16)));
emit("CL", Str("n=95 family=public_N map=e=N fate=leftover_shaped e=", N, " gcd_e_lam=", gcd(N,lam), " lam_div_e-1=", (N-1)%lam==0));
emit("CL", Str("n=96 family=public_N map=e=N-2 fate=shares_lambda e=", N-2, " gcd_e_lam=", gcd(N-2,lam)));
emit("CL", Str("n=97 family=public_N map=x=N-1 fate=miss x=", N-1, " x^3=", powm(N-1,3), " hit=", powm(N-1,e)==y));
emit("CL", Str("n=98 family=public_N map=floor_sqrt_N fate=miss x=", sqrtint(N), " x^3=", powm(sqrtint(N),3)));
phi3N=N^2+N+1;
emit("CL", Str("n=99 family=public_N map=Phi_3(N) fate=leftover_shaped e=", phi3N, " gcd_e_lam=", gcd(phi3N,lam)));
emit("CL", Str("n=100 family=dl map=base3 fate=leftover y=3^46=", powm(3,46), " x=3^42=", powm(3,42), " a*e_mod_lam=", (42*3)%lam, " c=46 sagm_both=", ((42*3)%lam)==46));

P77=extra_77();
emit("EXTRA", Str("id=77 N=", P77[1], " y=", P77[2], " x=", P77[3], " e=", P77[4], " lam=", P77[5], " residual=", extra_77_residual(), " default_N=", N));
emit("EXTRA", Str("id=253 N=", extra_253()[1], " lam=", extra_253()[2], " p_mod8=", 11%8, " q_mod8=", 23%8, " default_N=", N));
emit("EXTRA", Str("id=45 N=", extra_45()[1], " lam=", extra_45()[2], " ok=", extra_45_ok()));
emit("EXTRA", Str("id=105 N=", extra_105()[1], " lam=", extra_105()[2], " gcd(3,lam)=", gcd(3,extra_105()[2])));
emit("EXTRA", Str("id=247 N=", extra_247()[1], " lam=", extra_247()[2], " gcd(187,247)=", gcd(N, extra_247()[1])));
emit("EXTRA", Str("id=Nsq N=", extra_Nsq()[1], " (1+N)=", 1+N));

emit("WHOLE", Str("whole=", whole(), " residual=", residual(), " factor_from_x=", factor_from_x(), " peel_all=", peel_all(), " classes_all=", classes_all()));
