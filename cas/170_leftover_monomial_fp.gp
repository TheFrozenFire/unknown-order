\\ Leftover short-window monomial c X^{d_q} cannot invert F_p*:
\\ invert at 1 forces c^e ≡ 1, invert at 2 then forces
\\ 2^{d_q e} ≡ 2 (mod p), which is false.  This does *not* need
\\ d_q ≡ 1 (mod p−1) (that was 11×17 accident: d_q = p).
\\ Checked on frozen pins 187, 1363, 2491.  Mirrors SrsaRootPoly.v.
\\ Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

\\ --- campaign pin (alias of pin187) ---
p=pin_p; q=pin_q; e=pin_e; db=pin_inv3_q; da=pin_inv3_p;
check(db < q-2,                         "campaign d_q < q−2");
check(gcd(2,p)==1,                      "campaign 2 is a unit of F_p");
check(lift(Mod(2,p)^(db*e)) != 2%p,     "campaign 2^{d_q e} ≢ 2 (mod p)");
check((e*da)%(p-1)==1,                  "campaign d_p is the local inverse");
check((db%(p-1)) != (da%(p-1)),         "campaign d_q ≢ d_p (mod p−1)");
\\ old accident: X^{d_q}≡X on F_p* holds here because d_q=p
check(lift(Mod(2,p)^db)==2%p,           "campaign 187-accident: 2^{d_q}≡2 (mod p)");

\\ leftover: c^e≡1 ⇒ (c 2^{d_q})^e ≡ 2^{d_q e} ≢ 2
c=1;
check(lift(Mod(c,p)^e)==1,              "campaign c=1 has c^e≡1");
check(lift(Mod(c*lift(Mod(2,p)^db),p)^e) != 2%p, "campaign leftover misses 2");

\\ --- pin1363: the accident 2^{d_q}≡2 is false; the generic test holds ---
p=pin1363_p; q=pin1363_q; e=pin1363_e; db=pin1363_inv3_q; da=pin1363_inv3_p;
check(db < q-2,                         "1363 d_q < q−2");
check(gcd(2,p)==1,                      "1363 2 is a unit of F_p");
check(lift(Mod(2,p)^(db*e)) != 2%p,     "1363 2^{d_q e} ≢ 2 (mod p)");
check(lift(Mod(2,p)^db) != 2%p,         "1363 2^{d_q} ≢ 2 (mod p) (accident gone)");
check((db%(p-1)) != (da%(p-1)),         "1363 d_q ≢ d_p (mod p−1)");
c=1;
check(lift(Mod(c*lift(Mod(2,p)^db),p)^e) != 2%p, "1363 leftover misses 2");

\\ --- pin2491 ---
p=pin2491_p; q=pin2491_q; e=pin2491_e; db=pin2491_inv3_q; da=pin2491_inv3_p;
check(db < q-2,                         "2491 d_q < q−2");
check(gcd(2,p)==1,                      "2491 2 is a unit of F_p");
check(lift(Mod(2,p)^(db*e)) != 2%p,     "2491 2^{d_q e} ≢ 2 (mod p)");
check(lift(Mod(2,p)^db) != 2%p,         "2491 2^{d_q} ≢ 2 (mod p) (accident gone)");
check((db%(p-1)) != (da%(p-1)),         "2491 d_q ≢ d_p (mod p−1)");
c=1;
check(lift(Mod(c*lift(Mod(2,p)^db),p)^e) != 2%p, "2491 leftover misses 2");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
