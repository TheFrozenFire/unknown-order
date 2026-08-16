\\ CAS witnesses — cyclotomic Type-B handles Phi_n(p).
\\ Mirrors Cyclotomic.v.  n=1 is Pollard; n=2 is Williams; n=3,4,6
\\ are the next cheap extension-field periods.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

cyc1(p) = p-1;
cyc2(p) = p+1;
cyc3(p) = p*p + p + 1;
cyc4(p) = p*p + 1;
cyc6(p) = p*p - p + 1;

is_smooth(n, B) = {
  if(n <= 1, return(0));
  f = factor(n);
  for(i = 1, matsize(f)[1], if(f[i,1] > B, return(0)));
  1
};

maxpf(n) = { f = factor(n); f[matsize(f)[1], 1] };

\\ ring identities on a range of p
id_fail = 0;
for(p = 2, 80, \
  if(p*p-1 != cyc1(p)*cyc2(p), id_fail++); \
  if(p*p*p-1 != cyc1(p)*cyc3(p), id_fail++); \
  if(p^4-1 != cyc1(p)*cyc2(p)*cyc4(p), id_fail++); \
  if(p^6-1 != cyc1(p)*cyc2(p)*cyc3(p)*cyc6(p), id_fail++) \
);
check(id_fail == 0,                     "Phi-product identities on p=2..80");

\\ 47 is safe (Phi_1 = 46 = 2*23) but Phi_2 = 48 is 3-smooth
p = 47;
check(isprime(p) && isprime((p-1)\2),   "47 is safe");
check(!is_smooth(cyc1(p), 10),          "Phi_1(47)=46 is not 10-smooth");
check(is_smooth(cyc2(p), 10),           "Phi_2(47)=48 IS 10-smooth (Williams handle)");
check(maxpf(cyc1(p)) == 23,             "largest prime factor of 46 is 23");

\\ p=653: Phi_1=652=4*163, Phi_2=654=6*109, Phi_3=427063 is 19-smooth.
\\ Strong-prime checks (Phi_1 and Phi_2) miss the Phi_3 handle.
p3 = 653; B = 20;
check(isprime(p3),                      "653 prime");
check(!is_smooth(cyc1(p3), B),          "Phi_1(653) is not 20-smooth");
check(!is_smooth(cyc2(p3), B),          "Phi_2(653) is not 20-smooth");
check(is_smooth(cyc3(p3), B),           "Phi_3(653) IS 20-smooth");
check(maxpf(cyc1(p3)) == 163,           "Phi_1 largest prime factor 163");
check(maxpf(cyc2(p3)) == 109,           "Phi_2 largest prime factor 109");
check(maxpf(cyc3(p3)) == 19,            "Phi_3 largest prime factor 19");
printf("  [cyc] p=653 Phi_3=%d = %s\n", cyc3(p3), Str(factor(cyc3(p3))));

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
