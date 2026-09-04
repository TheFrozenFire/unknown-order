\\ Local inverses d_p, d_q of residual e are d mod (p−1) and d mod (q−1).
\\ CRT of those residues recovers d mod λ.  A TM that writes both
\\ local inverses wrote the trapdoor exponent.  Not residual-solver ⇒
\\ factor.  Mirrors CRTRSA.v / SrsaRootPoly.v.  Probe names avoid
\\ the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p=pin_p; q=pin_q; N=pin_N; e=pin_e; d=pin_d; lam=pin_lam;
da=pin_inv3_p; db=pin_inv3_q;

check(d%(p-1)==da,                      "d ≡ d_p (mod p−1)");
check(d%(q-1)==db,                      "d ≡ d_q (mod q−1)");
check((e*da)%(p-1)==1,                  "e·d_p ≡ 1 (mod p−1)");
check((e*db)%(q-1)==1,                  "e·d_q ≡ 1 (mod q−1)");
check((e*d)%lam==1,                     "e·d ≡ 1 (mod λ)");
crt187=lift(chinese(Mod(da,p-1), Mod(db,q-1)));
check(crt187==d%lam,                    "CRT(d_p, d_q) = d mod λ");

x=d+lam;
check(x%(p-1)==da,                      "d+λ still ≡ d_p (mod p−1)");
check(x%(q-1)==db,                      "d+λ still ≡ d_q (mod q−1)");
check(x%lam==d%lam,                     "d+λ ≡ d (mod λ)");

\\ inverse uniqueness: any local inverse is d mod (p−1)
da2=da+(p-1);
check((e*da2)%(p-1)==1,                 "d_p+(p−1) is still a local inverse");
check(da2%(p-1)==d%(p-1),               "it is d mod (p−1)");

\\ 1363 and 2491: same CRT identity
check(pin1363_d%(pin1363_p-1)==pin1363_inv3_p, "1363 d ≡ d_p (mod p−1)");
check(pin1363_d%(pin1363_q-1)==pin1363_inv3_q, "1363 d ≡ d_q (mod q−1)");
crt1363=lift(chinese(Mod(pin1363_inv3_p, pin1363_p-1), Mod(pin1363_inv3_q, pin1363_q-1)));
check(crt1363==pin1363_d%pin1363_lam,   "1363 CRT(d_p, d_q) = d mod λ");
check(pin2491_d%(pin2491_p-1)==pin2491_inv3_p, "2491 d ≡ d_p (mod p−1)");
check(pin2491_d%(pin2491_q-1)==pin2491_inv3_q, "2491 d ≡ d_q (mod q−1)");
crt2491=lift(chinese(Mod(pin2491_inv3_p, pin2491_p-1), Mod(pin2491_inv3_q, pin2491_q-1)));
check(crt2491==pin2491_d%pin2491_lam,   "2491 CRT(d_p, d_q) = d mod λ");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
