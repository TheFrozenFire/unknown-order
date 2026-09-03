\\ CAS witnesses — orders as objects.  Mirrors Order.v.
\\ Completeness of lcm-of-orders = λ is exhaustive on small N.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

check(znorder(Mod(2,11))==10,           "ord_11(2)=10");
check(znorder(Mod(2,17))==8,            "ord_17(2)=8");
check(valuation(10,2)==1,               "v2(ord_11(2))=1 = height");
check(valuation(8,2)==3,                "v2(ord_17(2))=3 = height");

\\ lcm of all unit orders equals λ
lcm_unit_orders(N) = {
  L = 1;
  for(a = 1, N-1,
    if(gcd(a,N)==1, L = lcm(L, znorder(Mod(a,N))))
  );
  L
};

check(lcm_unit_orders(pin_N)==lcm(10,16), "11×17: lcm of orders is λ=80");
check(lcm_unit_orders(209)==lcm(10,18), "11×19: lcm of orders is λ=90");
check(lcm_unit_orders(41*73)==lcm(40,72), "41×73: lcm of orders is λ");

\\ a single generator of (Z/pZ)* has order p-1
check(znorder(Mod(2,11))==10,           "2 generates (Z/11Z)*");
check(znorder(Mod(2,17))==8,            "2 has order 8 on 17 (not 16)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
