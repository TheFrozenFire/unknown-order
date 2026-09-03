\\ Alternating bilinear pairing on cyclic mu_3 is trivial.
\\ Eval pairing e(x,k)=x^k has the exponent in the clear and is
\\ not alternating (e(omega,1)=omega).  Mirrors EvalPairing.v
\\ alternating_bilinear_mu3_trivial.  Named extra p=13 (cas/86);
\\ pin mu_3 is {1} because gcd(3,p-1)=1.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p = pin_91_p;
w = [1, 3, 9];
check(#w == 3,                            "mu_3(F_13*) has 3 elements");
check(lift(Mod(1,p)^3)==1,                "1 is in mu_3");
check(lift(Mod(3,p)^3)==1,                "3 is in mu_3");
check(lift(Mod(9,p)^3)==1,                "9 is in mu_3");

c3_mul(pp, ww) = {
  okc = 1;
  for(i = 1, 3, for(j = 1, 3,
    if(lift(Mod(ww[i]*ww[j], pp)) != ww[1 + ((i-1)+(j-1))%3], okc = 0)
  ));
  okc
};
check(c3_mul(p, w),                       "mu_3 is C_3 under multiply");

om = 3;
check(lift(Mod(om,p)^1) != 1,             "eval_pair(omega,1)=omega ≠ 1");
check(znorder(Mod(om,p)) == 3,            "order of omega is 3");
check(lift(Mod(om,p)^3) == 1,             "eval_pair(omega,3)=1");

\\ code[1..9] entries in {1,2,3} are C_3 labels for e(w_i, w_j)
left_ok(code, i, j, k) =
  code[1+3*((i+j-2)%3)+(k-1)] == 1+(code[1+3*(i-1)+(k-1)]-1 + code[1+3*(j-1)+(k-1)]-1)%3;
right_ok(code, i, j, k) =
  code[1+3*(i-1)+((j+k-2)%3)] == 1+(code[1+3*(i-1)+(j-1)]-1 + code[1+3*(i-1)+(k-1)]-1)%3;

is_bil(code) = {
  okc = 1;
  for(i = 1, 3, for(j = 1, 3, for(k = 1, 3,
    if(!left_ok(code, i, j, k), okc = 0)
  )));
  for(i = 1, 3, for(j = 1, 3, for(k = 1, 3,
    if(!right_ok(code, i, j, k), okc = 0)
  )));
  okc
};

is_alt(code) = code[1]==1 && code[5]==1 && code[9]==1;

mkcode(c) = vector(9, i, 1 + (c \ 3^(i-1)) % 3);

n_bil = 0;
for(c = 0, 3^9-1, if(is_bil(mkcode(c)), n_bil++));
n_alt = 0;
for(c = 0, 3^9-1, if(is_alt(mkcode(c)), n_alt++));
n_both = 0;
for(c = 0, 3^9-1, if(is_bil(mkcode(c)) && is_alt(mkcode(c)), n_both++));
trivial = vector(9, i, 1);
nontriv_both(c) = is_bil(mkcode(c)) && is_alt(mkcode(c)) && mkcode(c) != trivial;
n_both_nontriv = 0;
for(c = 0, 3^9-1, if(nontriv_both(c), n_both_nontriv++));

check(n_bil > 0,                          "some bilinear maps exist");
check(n_both == 1,                        "exactly one alternating bilinear map");
check(n_both_nontriv == 0,                "that map is the constant-1 pairing");
check(is_bil(trivial),                    "constant-1 is bilinear");
check(is_alt(trivial),                    "constant-1 is alternating");

p2 = 11;
check((p2-1)%3 != 0,                      "pin: 3 does not divide 10");
n1 = 0;
for(x = 1, p2-1, if(lift(Mod(x,p2)^3)==1, n1++));
check(n1 == 1,                            "pin: only unit with x^3=1 is 1");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
