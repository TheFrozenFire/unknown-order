# Strong RSA — lift construction headlines off pin 187

Durable plan so a later session can pick slices without
re-deriving the lattice or regressing into “cannot prove.”
Companion to [`srsa.md`](srsa.md) (catalog of closed cuts),
[`hardness.md`](hardness.md),
[`generated/NAMED_SKIPS.md`](../generated/NAMED_SKIPS.md),
`rocq/Routes.v`.

This file is **not** a refuse of the live targets.
Unused `*_open_named` means unproved, on-goal. Proving one
is success. Compaction previously flattened that into
pessimism. Do not do that again.

Baseline when this plan was written: unknown-order `715c51d`,
CAS `01`–`254`, campaign pin 187 (`pin_p=11`, `pin_q=17`,
`pin_e=3`, `pin_d=27`, `pin_lam=80`). Working tree was clean.
Invert-all-units *structure* (window, Fermat folds, leftover
kernel, `N|c`) and unique unit `e`-th roots are already
theorems for distinct odd primes. GitHub issues #1–#6 are
closed.

The work here is the same shape as issue #4: theorems that
are really about distinct odd primes, still proved only at
187. It is **not** inhabiting an extraction named, not
another kernel-fold identity, and not another Dirichlet pin.

---

## Status (update the cell when a slice lands)

| ID | Slice | Status | Depends |
|---|---|---|---|
| S0 | Bézout `d'` for general `λ` (`residual_inv_mod_lam` off `pin_lam`) | done | — |
| S1 | Residual leaf at a unit of order `λ` extracts `d'` and `miller_walk`s, for general distinct odd primes | done | S0 |
| S2 | `miller_search` hits because mixed `√1` exist, not because `vm_compute` says 2 works | done | S1 |
| S3 | Invert-all-units poly / poly-at-`e` constructs a factor off pin | done | S0, S1 |
| S4 | Reduced-units inverter Millers from a `k` read off Inv, not from `pin_d` | done | S1 |

S0–S4 landed (CAS `255`). Pin stays 187. The ten
`*_open_named` stay unused. Do not invent a leftover/fold/`K`
identity as a next chunk. Do not inhabit an `*_open_named`.
Default if the user says “go” without a slice id was **S0 then S1**;
that campaign is complete.

---

## How to read the classification (do not regress)

From `rocq/NamedSkips.v` / `THEORY.md`:

| Kind | Unused means |
|---|---|
| `*_open_named` | Live target. Unproved, on-goal. Proving or refuting the precise sentence is success. |
| `*_named` | This skip is not in use. Not impossibility. Nearby Gallina is allowed. |
| `NamedRefuse` | Out of model (ROM, PPT, NFS, LLL development, AM09-as-SM). |
| `Not [foo_open_named]` | This theorem does not inhabit the live target. |

Live unused targets (10): the three `RSAInstance` nameds, the
three extraction nameds, `pratt_complete_open_named`, and the
three compose opens. Pin theorems are not those nameds.

---

## Hard constraints (same campaign)

- RSA-land only. Do not treat GRA / GGM / SAGM as standard-model
  hardness. Do not inhabit `srsa_residual_leaf` as `Problem_Factor`
  without mismatch.
- The `*_open_named` stay **unused as hypotheses**. Do not inhabit
  them by projecting `rsa_p` / `pin_p`, by `Solve (N+1)` plus
  False-elim, or by miller-from-`λ` while pretending the solver
  constructed the multiple.
- Do not prove `~ forall Solve, exists f`. Miller-from-`d` makes
  `exists f` true independently of Solve.
- Named skips unused as hyps. Sequential `_CoqProject`. CAS-first
  PARI (`gp -q`). No nested `{ }` in for-loops; no multi-line
  `check()` args; `trap` is reserved. After a pin change, rebuild
  from `Pin.v`. After green: Print Assumptions Closed, regenerate
  coverage / named-skips / lint, commit+push **unknown-order**
  only (lift to `rocq-proofs` only if a reusable lemma is born).
- Pin stays 187 unless a leaf needs a named extra. Do not swap
  and leave it. Accident theorems use `pin187_*`. Construction
  identities use `pin_*`. Named extras (`pin_77`, `pin_209`) are
  not campaign retargets.
- Do not delete CAS `01`–`n`. Do not extend `whole()` past the
  first hundred. Do not resume geometric-kernel / Fermat-fold
  coefficient identities as a “next chunk.”
- `orders_generate_lambda_named`, `eval_pair_needs_integer_named`,
  `pot_bilinear_verify_named` stay unused as hyps.
- Cyclicity is not a hypothesis. No SHA / ROM / PPT / NFS / LLL
  as theorems. Sequential-base Miller’s polynomial runtime is
  ERH-conditional; do not claim the ERH bound
  (`Miller.v` already says this).

---

## What already closed (do not redo)

On **this pin**, a single residual leaf at a unit of order `λ`
extracts `d'` by discrete log and Millers
(`residual_leaf_at_g_extracts_and_factors`,
`residual_solver_reduced_constructs_factor_pin`, CAS 240–241,
248). Every reduced residual solver therefore factors, including
varying-`e` and non-homomorphic ones. Homomorphic residual and
public-`e` reduced-units inverter are corollaries (`SrsaHom.v`).
Annihilator-`e` Strong RSA (`λ | e−1`) Millers from `e−1`;
residual forbids that class.

Already general (keep; pin theorems are wrappers):

| Piece | Theorem |
|---|---|
| Unique unit `e`-th roots | `unique_unit_eth_root_coprime` |
| Sharp window `deg < q−2`; no invert poly of `deg < d_q` | `short_root_poly_coeff_splits`, `no_root_poly_below_dq` |
| Fermat folds are local inverse monomials | `invert_all_units_folds_local_monomials` |
| Leftover kernel monic / 1-dimensional span | `leftover_monic_is_geo_kernel`, `leftover_kernel_span_mod_q` |
| Binomial `+ c K` inverts iff `N \| c` | `invert_all_units_plus_c_kernel_iff` |
| Miller square-chain from `(N,M,a)` | `miller_walk`, `miller_walk_factors` (takes an `RSAInstance`) |
| Mixed `√1` | `four_sqrt1` |
| A unit of order `λ` | `exists_unit_order_lambda` |
| Pratt verifier given `(g, qs)` | `pratt_verifier` |

Window extras that stay: `p < q < 2p` (honest `q−2` sample
count); `0 < e`; `2 < p` and `2 < q`; leftover-monomial branch
`powm 2 (dq * e) p <> 2 mod p`. Do not drop `q < 2p` to
“match an issue body.”

**Stale leftover, do not re-learn.** “Varying-`e` non-hom remains”
is false on this pin. Invert-all-units *structure* is no longer
pin-only. Dirichlet compose pins (`{id,f,f}`, `Cl(−31)` order 3,
`(5,5,24)∘(7,7,18)` on `−455`) are done; do not invent another.

---

## What is still actually open (not this campaign)

Three remainders. This plan does **not** close them. Do not
flatten them into S0–S4.

### 1. The six RSA nameds

- `rsa_inverter_extracts_factor_open_named` is `forall N e Inv`
  with **no `λ`**. Uniqueness of unit `e`-th roots needs
  `gcd(e,λ)=1`. That is the standard-model RSA ≡ factoring
  question. Rabin `e=2` is `rabin_oracle_nonassociate_factors`.
- `residual_solver_extracts_factor_open_named` still has `lam`
  in the type. Miller-from-`λ` inhabits `exists f` without
  touching Solve. Do not inhabit that way.
- `strong_rsa_solver_extracts_factor_open_named` has no `λ`.
  `(y, λ+1)` inhabits and does not gcd-split
  (`pin_lambda_strong_solver`). Do not prove
  `~ forall Solve, exists f`.
- The three `RSAInstance` nameds stay instance-vacuous
  (`rsa_p` inhabits them).

S0–S4 stay `Not [those nameds]`. Finding a generator `g` of
order `λ` from `(N,λ)` without `p,q` is a different slice
and is circular: miller-from-`λ` already factors.

Do **not** prove “`miller_search N λ` always returns `Some`
for every `RSAInstance`” and then call that the residual
extraction named. That is miller-from-`λ` for all instances;
`exists f` would again ignore Solve.

### 2. Pratt completeness

`pratt_complete_open_named` existentially factorizes `p−1`
for every prime. The verifier given that list is already a
theorem. Constructing the list for all `p` is factoring `p−1`.
Not S0–S4.

### 3. Dirichlet forall compose / assoc / left-compat

The remaining nameds are the *foralls*, not another pin.
Stop inventing Dirichlet pins.

[`pairing.md`](pairing.md) is a different campaign (CRS
checks, not residual solvers).

---

## Slices

Each slice: goal, why it is not leftover identities, files,
suggested names, CAS, honest-closure sentence, stop.

Suggested next CAS numbers start at 255. Do not reuse 01–254.

### S0 — Bézout `d'` for general `λ`

**Goal.** `gcd(e, λ)=1` ⇒ exists `d'` with `0 ≤ d' < λ` and
`e d' ≡ 1 (mod λ)`, for a positive `λ` (not only `pin_lam`).
Rebuild `residual_inv_mod_lam` as that general lemma; keep
the pin name as a wrapper, or apply the general lemma at
`pin_lam`.

**Why.** Every later extract-then-Miller headline threads
this inverse. The pin proof is already `Z.gcd_bezout`; it
does not use 80 except as the modulus. Cheap prerequisite
for S1/S3.

**Files.** `SrsaVaryingE.v`. Optional: `NumberTheory.v` in
`rocq-proofs` only if a second consumer appears in the same
turn (it should not).

**Suggested.** `residual_inv_mod_lambda` (or
`bezout_inv_mod`), pin wrapper `residual_inv_mod_lam`.

**CAS.** Reuse 238 arithmetic (`7·23 ≡ 1 (mod 80)`). A
second modulus (e.g. `λ=36` on 13×19, `e=5`, inverse 29)
if a new file is cleaner than rewriting 238.

**Honest closure.** Not the open nameds. Miller still uses
`(e,λ)`, not the solver’s `x`-values. Comment that.

**Stop.** The general Bézout lemma is used by S1 or at least
`Check`ed in `Routes.v`. Print Assumptions Closed. Pin 187
wrapper still holds.

### S1 — Residual leaf at a unit of order `λ`, off pin

**Goal.** Given distinct odd primes `p,q`, a unit `g` of
order `λ(pq)`, and a residual leaf `(x,e)` at `g`: uniqueness
plus Bézout give `x ≡ g^{d'}`; `dlog_search` reads `d'`;
`miller_walk (p*q) (e d'−1) a` returns a factor when base
`a` has mismatched 2-heights at `odd_part(e d'−1)`.

Then: any reduced residual solver supplies such a leaf at
`g`, so every reduced residual solver constructs a factor
*under those hyps* (including a height-mismatching base).

Pin 187 becomes a wrapper: `g = pin_g`, `a = 2`.

**Why.** This is the campaign’s strongest RSA theorem, still
proved only at 187. Unique-eth, miller walk, mixed `√1`,
and invert-all-units *structure* are already general. The
extract-then-Miller *headline* is not. Not leftover
coefficients of `K`.

**Files.** `SrsaExtractD.v` (general lemma) and pin wrappers
in the same file. Reuse `unique_unit_eth_root_coprime`,
S0, `dlog_search` (already general; `pin_dlog_mod_lam` is
the pin wrapper), `miller_walk_factors`.
`exists_unit_order_lambda` constructs *some* `g` from `p,q`;
do not pretend that construction is from `(N,λ)` without
factors.

**Suggested.** `residual_leaf_at_g_extracts_and_factors` stays
the pin wrapper; new
`residual_leaf_order_lambda_extracts_and_factors` (or similar)
for general `p,q,g,a`. Solver corollary
`residual_solver_reduced_constructs_factor` with the same
hyps; pin name remains `_pin`.

**CAS.** 13×19 (`N=247`, `λ=36`, residual `e=5`) with a
hitting base (2 if it mismatches there; otherwise the first
hit, analogously to Q3). Witness that dlog of the leaf at a
max-order unit recovers the inverse, and the walk — not
`2^{t 2^{kp}}` — is the gcd. Next free number: 255.

**Honest closure.** Not `residual_solver_extracts_factor_open_named`
(forall `N`, and miller-from-`λ` still ignores Solve). Not
the `RSAInstance` named (`exists f` would ignore Solve).
`g` of order `λ` is a hyp or comes from
`exists_unit_order_lambda` (uses `p,q`). The miller *proof*
may use heights; the miller *function* does not take `kp`.

**Stop.** General theorem plus pin wrapper. `Routes.v` Check.
Hom / inverter corollaries still call the pin name, or are
updated as wrappers, in this slice only if they compile
without further honesty work (that is S4). PA Closed.

### S2 — `miller_search` from mixed `√1`

**Goal.** `miller_search N M` is already a construction
(tries `a = 2 .. N−2`). Prove it hits for an `RSAInstance`
when `λ | M`, because mixed `√1` exist (`four_sqrt1`) and
a mixed `√1` is a miller-splitting base (heights `(0,1)` or
`(1,0)`). Pin `pin_miller_search` stays a wrapper that 2
hits here. Blum extra `11×19` already shows 2 can be a
liar and 3 hits; that is the existence, not `vm_compute`
on 187.

**Why.** S1 still takes a height-mismatching base as a hyp.
This slice drops hardcoded base 2 from the *search*, not
from the walk. Sequential-base Miller’s ERH runtime stays
unclaimed.

**Honesty.** Still miller-from-`λ` in the proof that *some*
base works. Do not inhabit the extraction named. Do not
prove the search for arbitrary `(N,lam)` that are not an
RSA modulus and its Carmichael function.

**Files.** `Miller.v` / `MillerHeight.v`. Pin wrapper stays
in `Miller.v`. Optional: S1’s solver corollary can take
`miller_search` instead of a base hyp, in this slice or as
a one-line follow-up.

**CAS.** Reuse 246 (pin hit at 2) and 247 (Blum liar/hit).
A 13×19 search first-hit if S1’s CAS did not already record
it.

**Stop.** Named theorem plus `Routes.v`. PA Closed.

### S3 — Invert-all-units poly constructs a factor, off pin

**Goal.** A polynomial that inverts every unit at a residual
`e` is the trapdoor map `y ↦ y^{d'}` (uniqueness + S0).
`dlog_search` of `P(g)` at a unit `g` of order `λ` recovers
`d'`; `miller_walk` at `e d'−1` splits under S1/S2’s miller
hyps. Specialization: `invert_all_units_poly_at_e` off
`pin_lam`. Pin theorems
`all_units_root_poly_is_trapdoor_map`,
`invert_all_units_poly_constructs_factor`,
`pin_X23_poly_at_e_7` become wrappers.

**Why.** Issue #4 lifted the coefficient identities (window,
folds, leftover `K`, `N|c`). The Miller *headline* still
uses `pin_d` / `pin_g` / base 2. Issue #1 already made the
pin poly miller from dlog of `P(g)` rather than a hyp
`pin_d`; this slice is that construction for general `p,q`.

**Files.** `SrsaRootPoly.v` (trapdoor map + constructs_factor)
and `SrsaVaryingE.v` (poly-at-`e`). Nodiv / rational wrappers
can wait; they apply the poly theorem.

**CAS.** 13×19, `e=5`, monomial `X^{d'}` inverts every unit;
dlog at a max-order unit recovers `d'`; walk splits. Reuse
254’s modulus if the probes stay in one file with S1.

**Honest closure.** Not the open nameds. A solver is still
not given as a polynomial. Miller uses a `k` read off `P`.

**Stop.** General theorems plus pin wrappers. `Routes.v`.
PA Closed.

### S4 — Inverter Millers from Inv, not from `pin_d`

**Goal.** `rsa_inverter_reduced_units_constructs_factor`
still Millers from `pin_d` via `pin_miller_from_d_factors`.
The Hom corollary
`rsa_inverter_reduced_units_constructs_factor_pin` already
goes through `inverter_as_residual` and the pin residual
solver. Rebuild the original inverter theorem so the miller
multiple is read off Inv (leaf at `g`, or dlog of Inv(`g`)),
matching issue #1’s honesty repair for polynomials.

Optional in the same slice, if S1 exists: generalize
`inverter_as_residual` off `pin_e` / `pin_lam` under
`gcd(e,λ)=1`. That hyp is `λ`, so it is still not
`rsa_inverter_extracts_factor_open_named`.

**Why.** Same honesty gap as #1, for the inverter theorem.
Public-`e` inversion *is* a residual solver at that `e`.

**Files.** `SrsaInverter.v`, `SrsaHom.v`. Reuse S1.

**CAS.** Reuse 223 / 227 / 252 arithmetic; witness that the
walk uses a `k` from Inv(`g`), not a hyp `pin_d`.

**Honest closure.** Not `rsa_inverter_extracts_factor_open_named`
(no `λ` in that type; uniqueness needs `gcd(e,λ)=1`;
`inverter_as_residual` writes `λ`). Rabin `e=2` stays
`rabin_oracle_nonassociate_factors`.

**Stop.** The inverter theorem’s miller step does not take
`pin_d` as the multiple. Comment matches reality. PA Closed.

---

## Suggested pick order

Default if the user says “go” without a slice id:

1. **S0** then **S1** — Bézout, then leaf-at-`g` off pin.
   That is the remaining pin-specificity of “every reduced
   residual solver factors.”
2. **S2** — search from mixed `√1`, once S1 takes a base hyp.
3. **S3** — poly Miller headline, once S0/S1 exist.
4. **S4** — inverter honesty, once S1 exists.

If the user names a slice, do that slice, not this default.

---

## Death conditions (stop the slice, do not “complete” it)

- The proof millers from `pin_d` / `rsa_d` / `rsa_lambda`
  while the theorem’s comment claims the solver constructed
  the multiple. Fix the comment or the construction (S1/S4).
- The proof inhabits an `*_open_named`. Revert.
- The proof takes an `*_named` as a hypothesis. Revert.
- Campaign pin swapped and left off 187.
- `11×19` work implemented on `pin_77` as if base 2 were a
  liar there. It is not.
- CAS `gp` exits 0 with a syntax error. Fail the slice.
- A new C-class that already contains `d` or `λ` as a hyp
  and Millers from it, without extracting from Solve, is
  **P2-shaped**. Not S1 or S4.
- Leftover kernel `K`, Fermat-fold coefficients, related-`y`
  identities, interpolating the 160-point table: not a slice.
  Do not resume.
- Proving `~ forall Solve, exists f`. Revert.
- Proving `miller_search` for every `RSAInstance` and
  inhabiting `residual_solver_extracts_factor_open_named`
  with it. Revert; that ignores Solve.
- Another Dirichlet compose pin. Stop.
- Dropping `q < 2p` from a window theorem to “match” a
  sample count that is then false (residue `2p` in `1..q−1`).

---

## After each landed slice

1. `Not [the live open nameds]` on new subsections unless
   the slice actually inhabits one (it should not).
2. `Routes.v` `Check` new headlines.
3. CAS next free number, `README.md` count, `cas/01`–`n`
   in the README sentence.
4. One row in [`srsa.md`](srsa.md) §10 (and
   [`hardness.md`](hardness.md) if a relation arrow moved).
5. `bash rocq/gen-coverage.sh` (or `run-check.sh`);
   Print Assumptions Closed on new headlines.
6. Set this file’s status cell to **done** and the commit
   hash.
7. Commit+push unknown-order only.

---

## Compaction: read this first

You are in the unknown-order Strong RSA campaign. Invert-all-units
*structure* and unique unit `e`-th roots are off pin 187.
On pin 187 every reduced residual solver factors via a leaf
at `g`. The leftover is **not** “varying-`e` non-hom” and
**not** another fold/`K` identity. Next work is the status
table at the top of **this** file (S0 then S1), under the
hard constraints above. Pin 187. CAS 255+ as landed. Do not
inhabit the nameds. Do not resume kernel folds. Do not treat
GRA as standard-model hardness. Do not prove
`~ forall Solve, exists f`. Do not invent Dirichlet pins.
