\\ CAS — seed-tagged aux search; CRT residue; S_b nonempty.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

\\ domain separation is a tag, not a PRF
seed = 7;
check(2*seed + 0 != 2*seed + 1,          "domain tags separate");

\\ toy derive_aux: first odd primes > B=2 meeting split-ready
B = 2;
r = 3; s = 5; u = 7; v = 13; w = 19;
check(r>B && s>B && u>B && v>B && w>B,   "aux > B");
check(u%3==1 && v%4==1 && w%6==1,        "split-ready (7,13,19)");
M = 4*r*s*u*v*w;
a = 13099;
check(a%r==1 && a%s==s-1 && a%4==3,      "residue on r,s,4");
check((a*a+a+1)%u==0 && (a*a+1)%v==0 && (a*a-a+1)%w==0, "residue on Φ3/4/6");

b = 18;
kmin = (2^(b-1) - a + M - 1) \ M;
kmax = (2^b - 1 - a) \ M;
check(kmin <= kmax,                      "S_18 nonempty for this aux");
check(512 - 160 == 352,                  "κ=160, b=512: 352-bit index space");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
