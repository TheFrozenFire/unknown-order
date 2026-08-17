\\ CAS — placement interval on the second index; same-slot pair is out.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

p = 13099; qbad = 220579;
check(!(p <= qbad && qbad <= 2*p) && !(qbad <= p && p <= 2*qbad), "same-slot 13099,220579 not balanced");

q = 21611;
check(p <= q && q <= 2*p,                "cross-slot 13099,21611 is balanced");
check(abs(q-p) >= 2^13,                  "far at gap=13");

\\ place_lo = max(2^{b-1}, ceil(p/2)); place_hi = min(2^b-1, p-2^gap)
\\ at toy b=15, range [16384, 32768): 21611 is in range, 13099 is not
b = 15; gap = 13;
plo = max(2^(b-1), (p+1)\2);
phi = min(2^b-1, q - 2^gap);
\\ q is the larger; interval for a partner of q
ploq = max(2^(b-1), (q+1)\2);
phiq = min(2^b-1, q - 2^gap);
check(ploq <= p && p <= phiq || (p < 2^(b-1)), "13099 is below b=15 range (honest: interval uses range)");

\\ gap too large empties: 2^20 > 21611/2
check(21611 - 2^20 < (21611+1)\2,        "huge gap empties the far bound vs ceil(p/2)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
