\\ One predicate per enumerated class.  Fate of that shape on the pin
\\ (and named second moduli).  Requires init_pin() first.

cl_01() = {
  lift(Mod(36,N)^3)==93 && lift(Mod(93,N)^3)==70
  && gcd(70-36,N)==17
};
cl_02() = lift(Mod(145,N)^3)==151;
cl_03() = N\2==93 && abs(36-93)==57 && lift(Mod(57,N)^3)==63;
cl_04() = eulerphi(36)==12 && 12%2==0;
cl_05() = hammingweight(36)==2 && 2%2==0;
cl_06() = gcd(3,7)==1 && lift(Mod(42,N)^3)==36 && lift(Mod(60,N)^7)==36;
cl_07() = N^2==34969 && lift(Mod(1+N, N^2)^1)==1+N;
cl_08() = {
  my(V2 = 62*62-2, V3 = 62*(62*62-2)-62);
  V3==238142 && V3%N==91
};
cl_09() = 36%2==0;
cl_10() = lift(Mod(36,N)^3)==93 && 93!=42;
cl_11() = gcd(25,lam)==5 && 25%2==1;
cl_12() = 2^9 > N && 42 >= 2;

cl_13() = lift(Mod(36,N)^5)==100 && lift(Mod(100,N)^3)==111;
cl_14() = lift(Mod(36,N)^36)==135;
cl_15() = lift(Mod(36,N)^N)==42 && 187%40==27;
cl_16() = lift(Mod(36,N)^(N-1))==157;
cl_17() = lift(Mod(36,N)^(N+1))==16;
cl_18() = sqrtint(36)==6 && 6^2==36;
cl_19() = lift(Mod(18,N)^3)==35;
cl_20() = {
  fromdigits(Vecrev(binary(36)),2)==9 && lift(Mod(9,N)^3)==168
  && gcd(168-36,N)==11
  && fromdigits(Vecrev(binary(43)),2)==53
};
cl_21() = (36*35/2)%N==69;
cl_22() = lift(Mod(37,N)^3)==163;
cl_23() = fibonacci(36)%N==85 && gcd(85,N)==17 && lift(Mod(85,N)^3)==17;
cl_24() = lift(Mod(2,N)^36)==152 && lift(Mod(152,N)^3)==135 && gcd(135-36,N)==11;
cl_25() = lift(Mod(3,N)^36)==47;
cl_26() = (36^2+36+1)%N==24;
cl_27() = lift(Mod(26,N)^3)==185 && lift(Mod(185,N)^3)==179 && gcd(179-36,N)==11;
cl_28() = lift(1/Mod(93,N))==185 && lift(Mod(185,N)^3)==179 && gcd(179-36,N)==11;
cl_29() = {
  my(h = lift(chinese(Mod(1,11), Mod(36,17))));
  h==155 && gcd(h,N)==1 && lift(Mod(155,N)^3)==144
};
cl_30() = {
  my(m = lift(chinese(Mod(9,11), Mod(1,17))));
  m==86 && gcd(lift(Mod(m,N)^3)-36, N)==11
};
cl_31() = 36+28==64 && 4^3==64;
cl_32() = (36^2+1)%N==175;

cl_33() = lcm(2,6)==6 && 6%2==0;
cl_34() = 1+logint(36,2)==6 && 6%2==0;
cl_35() = numdiv(36)==9 && gcd(9,lam)==1;
cl_36() = sigma(36)==91 && gcd(91,lam)==1 && lift(Mod(25,N)^91)==36;
cl_37() = 6%2==0;
cl_38() = omega(36)==2 && 2%2==0;
cl_39() = bigomega(36)==4 && 4%2==0;
cl_40() = gcd(3,lam)==1 && lift(Mod(42,N)^3)==36;
cl_41() = 37>36 && gcd(37,lam)==1;
cl_42() = 36/4==9 && gcd(9,lam)==1;
cl_43() = 2*2+1==5 && gcd(5,lam)==5;
cl_44() = gcd(35,186)==1;
cl_45() = gcd(1333,lam)==1 && 1333%2==1;
cl_46() = valuation(35,2)==0 && 2*valuation(36,2)+1==5 && gcd(5,lam)==5;
cl_47() = gcd(63,lam)==1 && 63%2==1 && lift(Mod(9,N)^63)==36;
cl_48() = N%36==7 && gcd(7,lam)==1 && lift(Mod(60,N)^7)==36;
cl_49() = 33==2^5+1 && gcd(33,lam)==1 && lift(Mod(53,N)^33)==36;
cl_50() = 2*3*5==30 && 30%2==0;

cl_51() = (3*27-1)%10==0;
cl_52() = (11-17)^2==28^2-4*N;
cl_53() = 6^2==36 && gcd(28-6,N)==11;
cl_54() = znorder(Mod(3,N))==lam;
cl_55() = factor(10)[1,1]==2;
cl_56() = factor(186)==[2,1;3,1;31,1];
cl_57() = 27>4;
cl_58() = lift(Mod(2,N)^80)==1;
cl_59() = {
  valuation(znorder(Mod(2,11)),2)==1
  && valuation(znorder(Mod(2,17)),2)==3
};
cl_60() = znprimroot(11)==2;
cl_61() = 42>>3==5 && 42%8==2;
cl_62() = kronecker(36,N)==1;

cl_63() = lift(Mod(49,N)^3)==26 && lift(1/Mod(42,N))==49;
cl_64() = (-36)%N==151;
cl_65() = 72==2*36;
cl_66() = gcd(3,5)==1;
cl_67() = lift(Mod(126,N)^3)==37;
cl_68() = gcd(42-60,N)==1;
cl_69() = 81==lam+1;
cl_70() = gcd(N,247)==1 && 36%247==36;
cl_71() = gcd(3,5)==1;
cl_72() = (42*60)%N==89 && lift(Mod(89,N)^3)==166;
cl_73() = e==3;
cl_74() = e==3 && residual();

cl_75() = gcd(lift(Mod(2,N)^60)-1,N)==11 && 60%16!=0 && 60%10==0;
cl_76() = {
  my(t=26, h=180);
  gcd(t-h,N)==11 && (2*2+1)==5 && (5*5+1)==26
};
cl_77() = lam != N-1;
cl_78() = 14^2-N==9 && issquare(9) && (14-3)==11 && (14+3)==17;
cl_79() = N%11==0 && 11>1 && 11<N;
cl_80() = {
  my(Vnm2=2, Vnm1=5, V, n);
  for(n=2,12, V=5*Vnm1-Vnm2; Vnm2=Vnm1; Vnm1=V);
  gcd(Vnm1-2,N)==11
};
cl_81() = gcd(lift(Mod(2,N)^186)-1,N)==1;
cl_82() = lift(Mod(2,N)^8)==256%N;
cl_83() = 36%2==0;
cl_84() = 36%2==0;

cl_85() = 3*3*5==45 && lift(Mod(1+3,9)^2)==(1+2*3)%9;
cl_86() = N*N*N==6539203;
cl_87() = kronecker(36,N)==1;
cl_88() = 17*17==289 && lift(Mod(2,17)^11)==8;
cl_89() = 7*23==161 && lcm(6,22)==66 && gcd(3,66)==3;
cl_90() = 11%8==3 && 23%8==7;
cl_91() = 101+103==204 && 204/2==102;
cl_92() = 11*101==1111 && 1111%11==0;
cl_93() = 3*5*7==105 && lcm(lcm(2,4),6)==12 && gcd(3,12)==3;
cl_94() = isprime(17) && gcd(3,16)==1 && lift(Mod(2,17)^11)==8;

cl_95() = gcd(N,lam)==1 && (N-1)%lam != 0;
cl_96() = gcd(N-2,lam)==5;
cl_97() = lift(Mod(-1,N)^3)==N-1;
cl_98() = sqrtint(N)==13 && lift(Mod(13,N)^3)==140;
cl_99() = gcd(N^2+N+1, lam)==1;
cl_100() = {
  lift(Mod(3,N)^46)==36 && lift(Mod(3,N)^42)==42
  && (42*3)%lam==46
};

class_vec() = [\
  cl_01, cl_02, cl_03, cl_04, cl_05, cl_06, cl_07, cl_08, cl_09, cl_10,\
  cl_11, cl_12, cl_13, cl_14, cl_15, cl_16, cl_17, cl_18, cl_19, cl_20,\
  cl_21, cl_22, cl_23, cl_24, cl_25, cl_26, cl_27, cl_28, cl_29, cl_30,\
  cl_31, cl_32, cl_33, cl_34, cl_35, cl_36, cl_37, cl_38, cl_39, cl_40,\
  cl_41, cl_42, cl_43, cl_44, cl_45, cl_46, cl_47, cl_48, cl_49, cl_50,\
  cl_51, cl_52, cl_53, cl_54, cl_55, cl_56, cl_57, cl_58, cl_59, cl_60,\
  cl_61, cl_62, cl_63, cl_64, cl_65, cl_66, cl_67, cl_68, cl_69, cl_70,\
  cl_71, cl_72, cl_73, cl_74, cl_75, cl_76, cl_77, cl_78, cl_79, cl_80,\
  cl_81, cl_82, cl_83, cl_84, cl_85, cl_86, cl_87, cl_88, cl_89, cl_90,\
  cl_91, cl_92, cl_93, cl_94, cl_95, cl_96, cl_97, cl_98, cl_99, cl_100\
];

classes_all() = {
  my(C=class_vec(), i, ok=1);
  for(i=1,#C, if(!C[i](), ok=0));
  ok
};

\\ Conjunction of fates on the pin: residual, not a factor, peel,
\\ and every named class.  Not a disjunction of solvers.
whole() = residual() && !factor_from_x() && peel_all() && classes_all();
