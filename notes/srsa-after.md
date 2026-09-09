# Strong RSA — after P0–P8

Durable plan so a later session can pick slices without
re-deriving the lattice or regressing into “cannot prove.”
Companion to `notes/srsa-next.md` (P0–P8, all done),
`notes/srsa-cuts.md`, `notes/hardness.md`,
`generated/NAMED_SKIPS.md`, `rocq/Routes.v`.

This file is **not** a refuse of the live targets.
Unused `*_open_named` means unproved, on-goal. Proving one
is success. Compaction previously flattened that into
pessimism. Do not do that again.

Baseline when this plan was written: unknown-order `d6fc9d4`,
CAS `01`–`244`, campaign pin 187 (`pin_p=11`, `pin_q=17`,
`pin_e=3`, `pin_d=27`, `pin_lam=80`). Working tree was clean
of Rocq/CAS edits.

---

## Status (update the cell when a slice lands)

| ID | Slice | Status | Depends |
|---|---|---|---|
| Q0 | Framing: P0–P8 leftover sentence is stale; remainder is Miller construction / other `N` / λ-free types | done | — |
| Q1 | Miller square-chain from `(N,M,a)` without a `kp` hyp from `p` | done | Q0 |
| Q2 | Finite miller-base search on this pin (`2..N−2`) | done | Q1 |
| Q3 | Blum / miller-liar named extra (`11×19`): matching-height base does not split; a different base does | done | Q1 |
| Q4 | Residual solver ⇒ factor under “this `(M,a)` millers,” not only pin-187 base 2 | done | Q1, Q2 |
| Q5 | Inverter remainder: `λ` is not in the type; pin theorem uses `pin_lam` | done | Q0 |
| Q6 | Strong-RSA remainder: `λ+1` inhabits without splitting; do not prove `~ forall` | done | Q0 |
| Q7 | Pratt completeness as given-factorization verifier, not `forall p` construction | done | — |
| Q8 | Dirichlet compose remaining branch (not RSA) | pending | — |

Pick **one slice per turn** unless the user says otherwise.
Do not skip a “Depends” cell. Do not invent a new leftover/fold/`K`
identity as a substitute for a slice. Do not inhabit an
`*_open_named`.

---

## How to read the classification (do not regress)

Same table as `notes/srsa-next.md`. Short form:

| Kind | Unused means |
|---|---|
| `*_open_named` | Live target. Unproved, on-goal. |
| `*_named` | This skip is not in use. Not impossibility. |
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
  identities use `pin_*`. Named extras (`pin_77`, a new `11×19`
  if Q3 needs it) are not campaign retargets.
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

## What P0–P8 actually closed (do not redo)

On **this pin**, a single residual leaf at a unit of order `λ`
extracts `d'` by discrete log and Millers
(`residual_leaf_at_g_extracts_and_factors`,
`residual_solver_reduced_constructs_factor_pin`, CAS 240–241).
Every reduced residual solver therefore factors, including
varying-`e` and non-homomorphic ones. Homomorphic residual and
public-`e` reduced-units inverter are corollaries (`SrsaHom.v`,
CAS 242). Annihilator-`e` Strong RSA (`λ | e−1`) Millers from
`e−1`; residual forbids that class (CAS 243).

Kernel: unique unit `e`-th roots from `gcd(e,λ)=1`
(`unique_unit_eth_root_from_coprime_e`); Bézout `d'`
(`residual_inv_mod_lam`); Win B at residual `e`
(`invert_all_units_poly_at_e`). Negative: `e=5` shares `λ`.

P7 added extraction nameds without `RSAInstance`. They stay
unused. P8 retargeted Pratt completeness and Dirichlet compose
to `*_open_named`; attained orders generate `λ` as a theorem
(`orders_attained_generate_lambda`); pin Pratt check on 11.

**Stale leftover, do not re-learn.** `notes/srsa-next.md`
§“What is still actually open” said the remainder of the
residual named was “a solver that varies `e` with `y` and is
not a homomorphism.” P5 closed that class *on this pin*. The
remainder is not another C-class restriction of the writer.

---

## What is still actually open (not a refuse)

Three different remainders. Do not flatten them.

### 1. Residual, on this pin: Miller’s *construction*

The pin residual theorem Millers from `e d'−1` with **base 2
at a hardcoded height** `val2(pin_ord2_p)`. That height is
read off `p`. `miller_seq` / `first_n_bases` exist in
`Miller.v` and are unused. `miller_try_base` is only
`gcd(a^t−1, N)`, not the square chain.

The algorithm Miller actually runs: from `(N,M,a)`, write
`M = 2^s · t` with `t` odd; set `g₀ ≡ a^t`; square; the first
non-`±1` square root of 1 is a mixed `√1` and gcd-splits.
That construction does not mention `p` or `kp`. The *proof*
that the gcd equals `p` still uses heights. Honest closure:
not the open nameds; `M` still came from Solve on this pin,
or was handed as a λ-multiple.

Base 2 works here because `v₂(ord_p 2)=1 ≠ v₂(ord_q 2)=3`
(`kg_2adic_unbalanced`). Unbalanced valuations do **not**
make every base a hit. `±1` always match.
`miller_150_of_158` / cyclic model: 150 mismatches among 160
units on this pin.

### 2. Residual, off this pin: miller-liar bases and other `N`

`height_mismatch_splits` is general. The pin theorem is not.
Blum `(1,1)` (`kg_blum_2adic`, Williams, safeprimes) has
mismatch 1/2 of units (`cyclic_mismatch_blum_11_19` on
`11×19`). Matched-deep `(3,3)` on `41×73` is 21/32
(`cyclic_mismatch_33`). Mixed `√1` still exist
(`four_sqrt1`); miller-from-`λ` still has *some* good bases.

`pin_77` (`7×11`) is Blum but base 2 still mismatches there
(`ord_7(2)=3`, `ord_11(2)=10`). Do not use it as a miller-liar
example. `11×19` is the tree’s Blum count; base 2 is a liar
(`ord_11(2)=10`, `ord_19(2)=18`, both `v₂=1`). Named extra,
not a campaign swap.

The extraction named
`residual_solver_extracts_factor_open_named` is `forall N lam
Solve`. Inhabiting it requires miller (or something else) for
every `N`. Matching-height bases fail; a finite search of
bases on an arbitrary `N` is the pin-finite construction
scaled up, not a proof of the forall. Do not inhabit.

`RSAInstance` nameds stay instance-vacuous.

### 3. Inverter and unrestricted Strong RSA: `λ` is not in the type

`rsa_inverter_extracts_factor_open_named` is `forall N e Inv`.
No `λ`. Uniqueness of unit `e`-th roots needs `gcd(e,λ)=1`.
Miller-from-`λ` needs `λ`. The pin inverter theorem
(`rsa_inverter_reduced_units_constructs_factor_pin`) goes
through `inverter_as_residual`, which uses `pin_lam` from the
module. That is not the extraction named. Rabin `e=2` is a
different theorem (`rabin_oracle_nonassociate_factors`).

`strong_rsa_solver_extracts_factor_open_named` is `forall N
Solve`. No `λ`. `(y, λ+1)` inhabits the solver type when `λ`
is known and does not gcd-split (`pin_lambda_strong_solver`).
Residual *excludes* that leaf. Do not prove
`~ forall Solve, exists f`.

This is the standard-model RSA ≡ factoring question for the
inverter, and the λ-trick obstruction for unrestricted
Strong RSA. Precise reductions stay the `*_open_named`s.
`Refuse_RSA_eq_factoring_standard_model` means: do not
*assume* the slogan.

### Side algebra (not the RSA nameds)

- **Pratt completeness.** `primitive_root_exists` is a theorem.
  `pratt_complete_open_named` asks for a generator, a prime
  factorization of `p−1`, and an inhabited `pratt`. Pin check
  on 11 is done. Forall-`p` construction of the factor list is
  factoring `p−1`. A verifier given `(g, qs)` is nearby and
  not the named.
- **Dirichlet compose.** Inverse pairs, unit leading coeff,
  `{id,f,f⁻¹}` are theorems. Remaining two-form branch is
  `compose_preserves_disc_open_named` /
  `compose_assoc_open_named` /
  `compose_left_compat_open_named`.

P4 interpolating polynomial (option B) is redundant on this
pin: leaf-at-`g` already factors every reduced residual
solver. Do not resume it as a substitute for Q1–Q4.

---

## Slices

Each slice: goal, why it is not leftover identities, files,
suggested names, CAS, honest-closure sentence, stop.

Suggested next CAS numbers start at 245. Do not reuse 01–244.

### Q0 — Framing hygiene

**Goal.** Stop the next compaction from re-learning “varying-`e`
non-hom remains.” Pointers from `README.md` “What is left”,
`THEORY.md` index, `notes/srsa-cuts.md`, `notes/hardness.md`,
`notes/rsa-land.md`, `notes/srsa-next.md` to this file.
Comment on `residual_solver_reduced_constructs_factor_pin`
that every reduced residual solver on this pin factors,
including varying-`e`. Do **not** inhabit the nameds.

**Why.** `srsa-next.md` leftover paragraph is false after P5.

**Files.** This file; pointer edits; optional one-line comment
in `SrsaExtractD.v` / `Routes.v`.

**Stop.** Pointers exist. No new theorem required.

### Q1 — Miller square-chain from `(N,M,a)`

**Goal.** A function that, given `N`, a positive `M`, and a
base `a`, walks `miller_seq` and returns `gcd(g−1, N)` at the
first mixed `√1`, or `None`. Theorem: if `λ | M` and the
2-heights of `a` at `odd_part(M)` mismatch, the function
returns `Some f` with `Problem_Factor N f`. Do not take `kp`
as an argument.

**Why.** Pin miller currently is
`gcd(2^{t · 2^{val2(pin_ord2_p)}}−1, N)`. That wrote `p` into
the exponent. The algorithm does not need it. `miller_seq` is
already defined and unused.

**Files.** `Miller.v` or `MillerHeight.v`. Pin wrapper in
`SrsaVaryingE.v` or a small `SrsaMillerWalk.v` before
`Routes.v`. Reuse `miller_splits`, `nontrivial_sqrt1_splits`,
`height_mismatch_splits`.

**Suggested.** `miller_walk`, `miller_walk_factors` (general
`RSAInstance` plus height mismatch), `pin_miller_walk_base2`
(no `kp` in the statement).

**CAS.** On pin 187, walk base 2 at `M=λ` hits mixed `√1=67`
or `120` and gcd-splits. Negative: `gcd(2^t−1, N)=1` so the
split is not at `g₀` (height 0 is false on the `p` side).

**Honest closure.** Not the open nameds. `M` is a given
λ-multiple. Construction does not mention `p`; the proof of
correctness may.

**Stop.** `Check pin_miller_walk_base2` in `Routes.v`. PA
Closed. `miller_try_base` either uses the walk or is
commented as the `g₀`-only special case.

### Q2 — Finite miller-base search on this pin

**Goal.** Search `a = 2, 3, …` until `miller_walk` returns
`Some f`. On this pin it hits at `a=2`. Theorem: exists `a`
in `2..N−2` such that the walk factors. Constructive: the
search function returns that `a`.

**Why.** Then miller does not hardcode “use 2.” Existence is
already the cyclic count plus `four_sqrt1`; the slice is the
*construction*. Sequential-base Miller is already described
in `Miller.v`; ERH runtime stays unclaimed.

**Honesty.** Still pin-finite. Not the forall-`N` extraction
named. `±1` are miller liars (`miller_splits` excludes them).

**CAS.** First hit is 2; a listed liar (e.g. 1, or a unit
with matching heights) returns `None`.

**Stop.** Named theorem plus `Routes.v`. PA Closed.

### Q3 — Blum miller-liar named extra

**Goal.** On `11×19` (already the Blum count in
`CyclicCount.v`): miller-from-`λ` with base 2 does **not**
split; some other base does. Residual leaf-at-`g` still
produces a λ-multiple `e d'−1`; the miller *step* needs a
good base.

**Why.** Documents that P5’s miller step is pin-specific in
the choice of base, not in the extraction of `M`. `pin_77`
is the wrong extra (base 2 still hits). Do not swap the
campaign pin. A frozen `pin209_*` (or similar) is a named
extra like `pin_77`.

**CAS.** `11×19`, `λ=90`, `v₂(ord_11 2)=1=v₂(ord_19 2)`;
`gcd(2^{t 2^k}−1, 209)` is 1 or 209 for the chain; a
mismatching base splits.

**Honest closure.** Not the open nameds. Negative for
“base 2 always millers.” Positive for “some base millers
on Blum.”

**Stop.** Named extra plus two theorems (liar / hit). PA
Closed. Campaign alias still 187.

### Q4 — Residual solver ⇒ factor under “this `(M,a)` millers”

**Goal.** Rebuild
`residual_solver_reduced_constructs_factor_pin` so the miller
step is `miller_walk N (e d'−1) a = Some f`, with `d'` from
Solve(`g`) as now. On this pin, `a=2` or Q2’s search.
Optional: the same statement on the Q3 extra with a hitting
base.

**Why.** Connects Q1–Q3 back to the residual solver. Still
not `residual_solver_extracts_factor_open_named` (forall `N`).
Still not the `RSAInstance` named.

**Honesty.** `g` of order `λ` is `pin_g` (module constant).
Finding such a `g` from `N,λ` without `p,q` is a different
slice; do not smuggle it in. Comment that.

**CAS.** Reuse 241 arithmetic; witness that the walk, not
`2^{t 2^{kp}}`, is the gcd.

**Stop.** Theorem used by the existing hom/inverter
corollaries, or they still call the old name as a wrapper.
`Not [the extraction nameds]`. PA Closed.

### Q5 — Inverter remainder, honestly scoped

**Goal.** Comments and one lattice Check: the pin inverter
theorem uses `pin_lam` via `inverter_as_residual`; the
extraction named has no `λ`; uniqueness needs
`gcd(e,λ)=1`; Rabin `e=2` is the other theorem. Optional:
a reduced-units inverter *given* `gcd(e,λ)=1` as a hyp
still factors on this pin by Q4 (the hyp is `λ`, so it is
not the extraction named).

**Why.** Stop compaction from reading
`rsa_inverter_reduced_units_constructs_factor_pin` as the
open named.

**Do not** inhabit `rsa_inverter_extracts_factor_open_named`.

**Stop.** `Routes.v` comments match reality. A new theorem
is optional; comments may suffice.

### Q6 — Strong-RSA remainder, honestly scoped

**Goal.** Same for `strong_rsa_solver_extracts_factor_open_named`.
`λ+1` inhabits and does not gcd-split. Annihilator-`e` is
the class that *does* miller, and residual excludes it.
Do **not** prove `~ forall Solve, exists f`.

**Stop.** Comments / Routes. No new C-class.

### Q7 — Pratt, given a factorization

**Goal.** If `p` is prime, `pratt_generator_ok p g qs`,
`pratt_factors_ok p qs`, and every `q ∈ qs` is prime, then
`inhabited (pratt p)` *and* `Z.prime p` is already the
soundness direction we have pieces of. Completeness of the
*verifier* given `(g,qs)` is not `pratt_complete_open_named`
(that one existentially factorizes `p−1`). Pin 11 already
has the checks. Recurse: each `q` needs its own cert.

**Why.** P8 retargeted the named; it did not prove the
verifier. Nearby algebra. `Not [pratt_complete_open_named]`
if the theorem takes `qs` as a hyp.

**Honesty.** Taking a factorization of `p−1` as a hyp is
honest. Constructing it for forall prime `p` is the named.

**CAS.** Reuse 244, or a second pin (e.g. 17 with `g=3`,
`qs=[2;8]` wait — 16=2^4, so `[2;2;2;2]` is the wrong
shape; Pratt wants the *distinct* prime factors `[2]`).
Prefer a pin whose `p−1` has two odd primes, or keep 11.

**Stop.** Verifier theorem or pin-only if general recursion
is too large. Named stays unused.

### Q8 — Dirichlet compose remaining branch

**Goal.** Either prove a named remaining case of
`compose_preserves_disc` / assoc / left-compat, or leave
them unused open. Not RSA. Only when not on Q1–Q6.

**Honesty.** `Not [the RSA nameds]`.

**Stop.** A Closed case, or no change.

---

## Suggested pick order

Default if the user says “go” without a slice id:

1. **Q0** with **Q1** — framing plus miller walk. Q0 is
   comments and can ride.
2. **Q2** then **Q3** then **Q4** — search, liar extra,
   residual solver uses the walk.
3. **Q5** and **Q6** when touching the nameds; comments
   may ride with Q4.
4. **Q7** / **Q8** when not on the RSA nameds.

If the user names a slice, do that slice, not this default.

---

## Death conditions (stop the slice, do not “complete” it)

- The proof millers from `pin_d` / `rsa_d` / `rsa_lambda`
  while the theorem’s comment claims the solver constructed
  the multiple. Fix the comment or the construction.
- The proof inhabits an `*_open_named`. Revert.
- The proof takes an `*_named` as a hypothesis. Revert.
- The miller walk still takes `kp` / `pin_ord2_p` as the
  exponent. That is the old theorem. Q1 failed.
- Campaign pin swapped and left off 187.
- `11×19` work implemented on `pin_77` as if base 2 were a
  liar there. It is not.
- CAS `gp` exits 0 with a syntax error. Fail the slice.
- A new C-class that already contains `d` or `λ` as a hyp
  and Millers from it, without extracting from Solve, is
  **P2-shaped**. Not Q4.
- Leftover kernel `K`, Fermat-fold coefficients, related-`y`
  identities, interpolating the 160-point table: not a slice.
  Do not resume.
- Proving `~ forall Solve, exists f`. Revert.

---

## After each landed slice

1. `Not [the live open nameds]` on new subsections unless
   the slice actually inhabits one (it should not).
2. `Routes.v` `Check` new headlines.
3. CAS next free number, `README.md` count, `cas/01`–`n`
   in the README sentence.
4. `notes/srsa-cuts.md` / `notes/hardness.md` one row.
5. `bash rocq/gen-coverage.sh` (or `run-check.sh`);
   Print Assumptions Closed on new headlines.
6. Set this file’s status cell to **done** and the commit
   hash.
7. Commit+push unknown-order only.

---

## Compaction: read this first

You are in the unknown-order Strong RSA campaign. P0–P8 of
`notes/srsa-next.md` are done. On pin 187 every reduced
residual solver factors via a leaf at `g`. The leftover is
**not** “varying-`e` non-hom.” Next work is the status
table at the top of **this** file, in the pick order above,
under the hard constraints above. Pin 187. CAS 244+ as
landed. Do not inhabit the nameds. Do not resume kernel
folds. Do not treat GRA as standard-model hardness.
Do not prove `~ forall Solve, exists f`.
