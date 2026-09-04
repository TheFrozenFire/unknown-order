\\ An invert-all-units monomial X^k has e k ≡ 1 (mod λ), and d is
\\ the inverse of e, so k ≡ d (mod λ) by uniqueness.  Writing such
\\ a k wrote d.  Not residual-solver ⇒ factor.  Mirrors
\\ SrsaRootPoly.v.  Probe names avoid the word "fail".

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

e=pin_e; d=pin_d; lam=pin_lam; N=pin_N;
da=pin_inv3_p; db=pin_inv3_q; p=pin_p; q=pin_q;

check((e*d)%lam==1,                     "e·d ≡ 1 (mod λ)");
k1=d+lam;
check((e*k1)%lam==1,                    "e·(d+λ) ≡ 1 (mod λ)");
check(k1%lam==d%lam,                    "d+λ ≡ d (mod λ)");
k2=d+2*lam;
check((e*k2)%lam==1,                    "e·(d+2λ) ≡ 1 (mod λ)");
check(k2%lam==d%lam,                    "d+2λ ≡ d (mod λ)");
check(d%lam==d,                         "d < λ so d mod λ = d");

crt=lift(chinese(Mod(da,p-1), Mod(db,q-1)));
check(crt==d%lam,                       "CRT of local inverses is d mod λ");

check((e*pin1363_d)%pin1363_lam==1,     "1363 e·d ≡ 1 (mod λ)");
k1363=pin1363_d+2*pin1363_lam;
k1363mod=k1363%pin1363_lam;
check(k1363mod==pin1363_d%pin1363_lam,  "1363 d+2λ ≡ d (mod λ)");
check((e*pin2491_d)%pin2491_lam==1,     "2491 e·d ≡ 1 (mod λ)");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
