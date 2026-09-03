#!/usr/bin/env python3
"""Rewrite Pin.v / cas/lib/pin.gp default-pin integers for a new p,q."""
import re, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PIN_V = ROOT / "rocq" / "Pin.v"
PIN_GP = ROOT / "cas" / "lib" / "pin.gp"

def gp(src: str) -> str:
    r = subprocess.run(["gp", "-q"], input=src, text=True, capture_output=True, cwd=str(ROOT / "cas"))
    if r.returncode != 0:
        sys.stderr.write(r.stderr)
        raise SystemExit(r.returncode)
    return r.stdout

def compute(p, q):
    src = rf"""
p={p}; q={q}; N=p*q;
lam=lcm(p-1,q-1); phi=(p-1)*(q-1);
e=3; d=lift(1/Mod(e,lam));
x=42;
if(gcd(x,N)!=1, x=2);
y=lift(Mod(x,N)^e);
s1=lift(chinese(Mod(1,p), Mod(-1,q)));
s2=lift(chinese(Mod(-1,p), Mod(1,q)));
g=3;
if(gcd(g,N)!=1, g=5);
gop=znorder(Mod(g,p)); goq=znorder(Mod(g,q));
yop=znorder(Mod(y,p)); yoq=znorder(Mod(y,q));
yo=znorder(Mod(y,N));
o2p=znorder(Mod(2,p)); o2q=znorder(Mod(2,q));
invp=lift(1/Mod(3,p-1)); invq=lift(1/Mod(3,q-1));
ca=q*lift(1/Mod(q,p)); cb=p*lift(1/Mod(p,q));
xk=znorder(Mod(x,p));
print("N=",N);
print("lam=",lam);
print("phi=",phi);
print("d=",d);
print("x=",x);
print("y=",y);
print("s1=",s1);
print("s2=",s2);
print("g=",g);
print("gop=",gop);
print("goq=",goq);
print("yop=",yop);
print("yoq=",yoq);
print("yo=",yo);
print("o2p=",o2p);
print("o2q=",o2q);
print("invp=",invp);
print("invq=",invq);
print("ca=",ca);
print("cb=",cb);
print("xk=",xk);
print("sqrtp=",sqrtint(p));
print("sqrtq=",sqrtint(q));
print("gcd3lam=",gcd(3,lam));
"""
    vals = {}
    for line in gp(src).splitlines():
        if "=" in line:
            k, v = line.split("=", 1)
            vals[k.strip()] = int(v.strip())
    # Dixon / asquare / NFS
    N = vals["N"]
    src2 = rf"""
p={p}; q={q}; N=p*q;
asq=0;
for(a=2,400, \
  rem=a^2%N; \
  if(issquare(rem), \
    t=sqrtint(rem); \
    gg=gcd(a-t,N); \
    if(gg>1 && gg<N && asq==0, print("asq_a=",a); print("asq_t=",t); asq=1) \
  ) \
);
found=0;
for(a=2,200, \
  r=a^2%N; \
  if(r==0 || issquare(r), next); \
  for(b=a+1,250, \
    s=b^2%N; \
    if(s==0 || issquare(s), next); \
    pr=r*s; \
    if(issquare(pr), \
      t=sqrtint(pr); \
      gg=gcd(a*b-t,N); \
      if(gg>1 && gg<N && found==0, \
        print("dx_a=",a); print("dx_b=",b); print("dx_r=",r); print("dx_s=",s); print("dx_t=",t); \
        found=1; A=a; R=r \
      ) \
    ) \
  ) \
);
if(found, \
  for(b=2,400, \
    if(b==dxb, next); \
    s=b^2%N; \
    pr=R*s; \
    if(issquare(pr) && s && !issquare(s), \
      t=sqrtint(pr); \
      gg=gcd(A*b-t,N); \
      if(gg>1 && gg<N, print("dx_b2=",b); print("dx_s2=",s); print("dx_t2=",t); break) \
    ) \
  ) \
);
m0=sqrtint(N);
c0=N-m0*(m0+1);
print("nfs_m=",m0); print("nfs_c0=",c0);
print("red_c0=",-q+1); print("red_c1=",p+q-2); print("red_m=",p+1);
"""
    # fix red: (m-r)(m-s)=N with r=1, m=p+1 => m-r=p, m-s=q => s=m-q
    # c1=-(1+s)=-(1+p+1-q)=q-p-2? Let me compute in gp below instead.
    out2 = gp(rf"""
p={p}; q={q}; N=p*q;
m=p+1; r=1; s=m-q;
print("red_c0=", r*s);
print("red_c1=", -(r+s));
print("red_m=", m);
m0=sqrtint(N);
print("nfs_m=",m0);
print("nfs_c0=", N-m0*(m0+1));
asq=0;
for(a=2,500, \
  rem=a^2%N; \
  if(issquare(rem), \
    t=sqrtint(rem); gg=gcd(a-t,N); \
    if(gg>1 && gg<N && asq==0, print("asq_a=",a); print("asq_t=",t); asq=1) \
  ) \
);
found=0; A=0; R=0;
for(a=2,180, \
  r=a^2%N; if(r==0 || issquare(r), next); \
  for(b=a+1,220, \
    s=b^2%N; if(s==0 || issquare(s), next); \
    pr=r*s; \
    if(issquare(pr), \
      t=sqrtint(pr); gg=gcd(a*b-t,N); \
      if(gg>1 && gg<N && found==0, \
        print("dx_a=",a); print("dx_b=",b); print("dx_r=",r); print("dx_s=",s); print("dx_t=",t); \
        found=1; A=a; R=r \
      ) \
    ) \
  ) \
);
if(found, \
  for(b=2,400, \
    if(b==0, next); \
    s=b^2%N; \
    if(s==0 || issquare(s), next); \
    pr=R*s; \
    if(issquare(pr), \
      t=sqrtint(pr); gg=gcd(A*b-t,N); \
      if(gg>1 && gg<N && b!=0, \
        if(b != 0, print("dx_b2=",b); print("dx_s2=",s); print("dx_t2=",t); break) \
      ) \
    ) \
  ) \
);
""")
    for line in out2.splitlines():
        if "=" in line:
            k, v = line.split("=", 1)
            try:
                vals[k.strip()] = int(v.strip())
            except ValueError:
                pass
    return vals

def disj(lo, hi):
    return " \\/ ".join(f"d = {i}" for i in range(lo, hi + 1))

def patch_v(text, vals, p, q):
    def nset(name, val):
        nonlocal text
        text, n = re.subn(
            rf"(Notation {name} := )-?\d+\.",
            rf"\g<1>{val}.",
            text,
            count=1,
        )
        if n != 1:
            raise SystemExit(f"failed to set {name}")
    nset("pin_p", p)
    nset("pin_q", q)
    nset("pin_d", vals["d"])
    nset("pin_y", vals["y"])
    nset("pin_x", vals["x"])
    nset("pin_lam", vals["lam"])
    nset("pin_phi", vals["phi"])
    nset("pin_g", vals["g"])
    nset("pin_g_ord_p", vals["gop"])
    nset("pin_g_ord_q", vals["goq"])
    nset("pin_y_ord", vals["yo"])
    nset("pin_y_ord_p", vals["yop"])
    nset("pin_y_ord_q", vals["yoq"])
    nset("pin_x_k", vals["xk"])
    nset("pin_inv3_p", vals["invp"])
    nset("pin_inv3_q", vals["invq"])
    nset("pin_ord2_p", vals["o2p"])
    nset("pin_ord2_q", vals["o2q"])
    text, n = re.subn(
        r"Definition pin_sqrt1_mixed : Z := -?\d+\.",
        f"Definition pin_sqrt1_mixed : Z := {vals['s1']}.",
        text, count=1,
    )
    text, n = re.subn(
        r"Definition pin_sqrt1_mixed2 : Z := -?\d+\.",
        f"Definition pin_sqrt1_mixed2 : Z := {vals['s2']}.",
        text, count=1,
    )
    # prime sqrt trials
    sp, sq = vals["sqrtp"], vals["sqrtq"]
    text, n = re.subn(
        r"change \(Z\.sqrt pin_p\) with \d+ in Hd\.\n  assert \(d = 2 \\/ d = 3(?: \\/ d = \d+)*\) by lia\.",
        "change (Z.sqrt pin_p) with %d in Hd.\n  assert (%s) by lia." % (sp, disj(2, sp)),
        text, count=1,
    )
    text, n = re.subn(
        r"change \(Z\.sqrt pin_q\) with \d+ in Hd\.\n  assert \(d = 2 \\/ d = 3(?: \\/ d = \d+)*\) by lia\.",
        "change (Z.sqrt pin_q) with %d in Hd.\n  assert (%s) by lia." % (sq, disj(2, sq)),
        text, count=1,
    )
    def dset(name, key):
        nonlocal text
        if key not in vals:
            return
        text, n = re.subn(
            rf"(Definition {name} : Z := )-?\d+\.",
            rf"\g<1>{vals[key]}.",
            text, count=1,
        )
    dset("pin_dixon_a", "dx_a")
    dset("pin_dixon_b", "dx_b")
    dset("pin_dixon_r", "dx_r")
    dset("pin_dixon_s", "dx_s")
    dset("pin_dixon_t", "dx_t")
    dset("pin_dixon_b2", "dx_b2")
    dset("pin_dixon_s2", "dx_s2")
    dset("pin_dixon_t2", "dx_t2")
    dset("pin_root_ca", "ca")
    dset("pin_root_cb", "cb")
    dset("pin_asquare_a", "asq_a")
    dset("pin_asquare_t", "asq_t")
    dset("pin_nfs_irr_c0", "nfs_c0")
    dset("pin_nfs_irr_m", "nfs_m")
    dset("pin_nfs_red_c0", "red_c0")
    dset("pin_nfs_red_c1", "red_c1")
    dset("pin_nfs_red_m", "red_m")
    return text

def patch_gp(text, vals, p, q):
    text = re.sub(r"pin_p = \d+; pin_q = \d+;", f"pin_p = {p}; pin_q = {q};", text, count=1)
    pairs = [
        ("pin_d", "d"), ("pin_y", "y"), ("pin_x", "x"),
        ("pin_lam", "lam"), ("pin_phi", "phi"),
        ("pin_g", "g"), ("pin_g_ord_p", "gop"), ("pin_g_ord_q", "goq"),
        ("pin_y_ord", "yo"), ("pin_x_k", "xk"),
        ("pin_inv3_p", "invp"), ("pin_inv3_q", "invq"),
        ("pin_root_ca", "ca"), ("pin_root_cb", "cb"),
        ("pin_ord2_p", "o2p"), ("pin_ord2_q", "o2q"),
        ("pin_sqrt1_mixed", "s1"), ("pin_sqrt1_mixed2", "s2"),
    ]
    for name, key in pairs:
        if key in vals:
            text = re.sub(rf"{name} = -?\d+", f"{name} = {vals[key]}", text, count=1)
    text = re.sub(r"pin_y_ord_p = \d+", f"pin_y_ord_p = {vals['yop']}", text, count=1)
    text = re.sub(r"pin_y_ord_q = \d+", f"pin_y_ord_q = {vals['yoq']}", text, count=1)
    return text

def main():
    p, q = int(sys.argv[1]), int(sys.argv[2])
    vals = compute(p, q)
    print(vals)
    if vals.get("gcd3lam", 1) != 1:
        raise SystemExit("gcd(3,λ)≠1 — not an e=3 pin")
    PIN_V.write_text(patch_v(PIN_V.read_text(), vals, p, q))
    gp_text = PIN_GP.read_text()
    # pin.gp may not have y_ord_p yet
    if "pin_y_ord_p" not in gp_text:
        gp_text = gp_text.replace(
            f"pin_y_ord = {vals['yo']}; pin_x_k",
            f"pin_y_ord = {vals['yo']}; pin_y_ord_p = {vals['yop']}; pin_y_ord_q = {vals['yoq']}; pin_x_k",
        )
    PIN_GP.write_text(patch_gp(gp_text, vals, p, q))
    print("patched", p, q, "N=", vals["N"])

if __name__ == "__main__":
    main()
