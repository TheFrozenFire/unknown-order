# Sieve relations that factored RSA numbers

RSA-challenge factorizations through RSA-250 share one last step:
manufacture `x² ≡ y² (mod N)` with `x ≢ ±y`, then `gcd(x−y, N)`
splits. That last step is already `rabin_roots_split` /
`nontrivial_sqrt1_splits`. `rocq/SieveRelation.v` is how QS and
NFS *build* the congruence. Integers come from `rocq/Pin.v` /
`cas/lib/pin.gp` (`pin_N`, Dixon bases, NFS coefficients). CAS `161`–`163`.

## Methods through RSA-250

| Era | Numbers | Method |
|---|---|---|
| 1991–1994 | RSA-100, 110, 120, 129 | MPQS / PPMPQS |
| 1996 | RSA-130 | first NFS on an RSA challenge |
| 1999–2005 | RSA-140, 155 (512-bit), 160, 576, 150, 200, 640 | GNFS |
| 2009–2018 | RSA-768, 170–230, 704 | GNFS, then CADO-NFS |
| 2019–2020 | RSA-240 (~900 core-years), RSA-250 (~2700 core-years) | CADO-NFS, Kleinjung polyselect, lattice sieving |

Sources: RSA Factoring Challenge table; Boudot–Gaudry–Guillevic–Heninger–Thomé–Zimmermann, arXiv 2006.06197 (RSA-240/250). RSA-240 used `Res(f₀,f₁)=120N`; RSA-250 used `Res=48N`; both deg-6 algebraic + linear rational.

## What is proved

- **Dixon / QS.** Even exponent vectors on B-smooth residues make a square (`even_nonneg_pow_square`). Two modular squares whose residues multiply to a square combine (`dixon_two_relations`). Pin names `pin_dixon_*` (`dixon_pin_splits`). CAS `161`.
- **NFS setup.** Quadratic remainder `F(a,b) − f(m) b² = (a−mb) H(a,b)` (`hom_quad_remainder`). If `N | f(m)` then `F ≡ GH (mod N)`. Coefficients `pin_nfs_irr_*` / `pin_nfs_red_*`. CAS `162`.
- **Two-sided combination.** `G`-product and `H`-product both squares ⇒ `F`-product is a square mod `N` (`nfs_two_sided_product`). Pairs `pin_ts_*` (`nfs_two_sided_splits`). CAS `163`.

Cost, smoothness probability, LLL polyselect, and “NFS factors RSA-250” as a runtime theorem are out of this file.
