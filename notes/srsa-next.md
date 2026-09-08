# Strong RSA — next work after the C-class campaign

Durable plan so a later session can pick slices without
re-deriving the lattice or regressing into “cannot prove.”
Companion to `notes/srsa-cuts.md` (what closed),
`notes/hardness.md` (relation arrows),
`generated/NAMED_SKIPS.md` (open / refuse / does-not-discharge),
`rocq/Routes.v` (compile-time pins).

This file is **not** a refuse of the three live targets.
Unused `*_open_named` means unproved, on-goal. Proving one is
success. Compaction previously flattened that into pessimism.
Do not do that again.

Baseline when this plan was written: unknown-order `9087aae`,
CAS `01`–`236`, campaign pin 187 (`pin_p=11`, `pin_q=17`,
`pin_e=3`, `pin_d=27`, `pin_lam=80`). Working tree was clean.

P1–P4 landed (CAS `237`–`240`). P3 is the uniqueness+Bézout path,
not Fermat folds at a general `e`. P4 dlog uses Bézout for
existence of `d'` and reads it off `Solve(g)`.

P5–P6: a residual leaf at generator `g` extracts `d'` by dlog
and Millers (`residual_solver_reduced_constructs_factor_pin`).
Every reduced residual solver on this pin factors; homomorphic
solvers and public-`e` inverters are corollaries. Not the
forall-`RSAInstance` open named (height mismatch is pin-specific).
Annihilator-`e` Strong-RSA solvers Miller from `e−1`; residual
forbids that class. Three `*_open_named` still unused.

---

## Status (update the cell when a slice lands)

| ID | Slice | Status | Depends |
|---|---|---|---|
| P0 | Framing: do not re-refuse live targets; comments on vacuity of the nameds as written | pending | — |
| P1 | Uniqueness of unit `e`-th roots from `gcd(e,λ)=1`, no handed inverse | done | — |
| P2 | Bézout `d'` from `(e,λ)`; drop `d'` hyp from the fixed-`e` theorem | done | P1 |
| P3 | Generalize Win B off `pin_e` (uniqueness + Bézout; folds of that `e` still open) | done | P1 |
| P4 | Recover `d` / `d'` from the solver’s `x`-values (local dlog or interpolant), then Miller | done | P1, P3 |
| P5 | Homomorphic residual solver ⇒ factor | done | P1, P3 |
| P6 | Lattice arrows among the three nameds; `λ \| e−1` Miller-from-`(e−1)` class | done | P2 or P4 |
| P7 | Re-type / re-comment the live targets so `exists f` is not instance-vacuous | pending | P0 |
| P8 | Stale `*_named` refuses that are deferred algebra (Pratt, orders, Dirichlet compose) | pending | — |

Pick **one slice per turn** unless the user says otherwise.
Do not skip a “Depends” cell. Do not invent a new leftover/fold/K
identity as a substitute for a slice.

---

## How to read the classification (do not regress)

From `rocq/NamedSkips.v` / `THEORY.md`:

| Kind | Unused means | Compaction failure |
|---|---|---|
| `Definition foo_open_named` | **Live target.** Unproved, on-goal. Proving or refuting the precise sentence is success. | Treating it as a wall / “cannot prove.” |
| `Definition foo_named` | This skip is **not in use**. Not a proof of impossibility. Nearby Gallina is allowed. | Moving it to `NamedRefuse` or writing “cannot prove.” |
| `NamedRefuse` constructor | **Out of model** (ROM, PPT, NFS, LLL *development*, AM09-as-standard-model). | Using it as a ban on a nearby reduction. |
| `(** **` `Not [foo_open_named]` | This theorem does not inhabit the live target. Honest scope. | Reading “Not” as “the target is refused.” |

`Refuse_RSA_eq_factoring_standard_model` means: do not *assume*
the slogan, and do not take AM09 as a standard-model proof.
Precise reductions are the `*_open_named`s, not that constructor.

RSA inversion ⇒ factoring is a famous standard-model open
problem. Rabin `e=2` reduces. Odd residual `e` has a unique unit
root, so the two-root gcd trick dies. That is an obstruction to
*one* proof idea. It is not a refuse of the Gallina target, and
it is not a proof that pin-finite interpolation plus Win B fails.

---

## Hard constraints (same campaign)

- RSA-land only. Do not treat GRA / GGM / SAGM as standard-model
  hardness. Do not inhabit `srsa_residual_leaf` as `Problem_Factor`
  without mismatch.
- The three `*_open_named` stay **unused as hypotheses**. Do not
  inhabit them by projecting `rsa_p` / `pin_p`, by `Solve (N+1)`
  plus False-elim, or by miller-from-`λ` while pretending the
  solver constructed the factor.
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
  identities use `pin_*`.
- Do not delete CAS `01`–`n`. Do not extend `whole()` past the
  first hundred. Do not resume geometric-kernel / Fermat-fold
  coefficient identities as a “next chunk.”
- `orders_generate_lambda_named` and `pratt_complete_named` stay
  **unused as hypotheses**. Slice P8 may *prove* nearby algebra
  or retarget them to `*_open_named`. It may not take them as hyps.
- Cyclicity is not a hypothesis. No SHA / ROM / PPT / NFS / LLL
  as theorems.

---

## What already closed (do not redo)

A leftover pair is not a factor (`matching_247_*`). Invert from
`ord(y)` always inhabits the residual leaf.

**Algebraic machines that invert every unit factor.**
Polynomial, nodiv GRA, rational, unit-`GInv` tape: trapdoor map
`y ↦ y^d`; Fermat folds are local inverse monomials; CRT recovers
`d`; Miller splits. `GInv` / integer `GRoot` / modular cube-root
of a non-unit leak a gcd. Win B:
`invert_all_units_poly_constructs_factor` (CAS 201) and wrappers
(CAS 202–214).

**Pinned exponent factors, with a handed inverse or public `e`.**
- Public `e` residual solver / reduced-units inverter: unique
  unit cube-root is `y^d`; Miller-from-`d` (CAS 220–223, 227).
- `e ≡ pin_e (mod λ)`: same `x`; non-minimal Millers from
  `e−pin_e` recovered from the solver (CAS 229, 233).
- Fixed residual `e` plus known inverse `d'`: trapdoor
  `y ↦ y^{d'}`; Miller-from-`e d'−1` (CAS 234–236). Miller uses
  the inverse, not the solver.

**λ-trick solves Strong RSA and does not gcd-split.**
`(y, λ+1)` inhabits; outputs never a proper gcd; not a residual
leaf (CAS 225, 226, 228). Miller-from-`d` still splits
independently.

**Arrows already in Rocq.**
`inverter_as_residual`, `strong_solver_as_inverter`,
`rsa_inverter_recovers_message`,
`rabin_oracle_nonassociate_factors`.
`primitive_root_exists`, `exists_unit_order_lambda` (general
`p,q`), `orders_generate_lambda_pin`.

Headline files: `SrsaRootPoly.v`, `SrsaResidualGRA.v`,
`SrsaModCbrt.v`, `SrsaInverter.v`, `SrsaVaryingE.v`,
`GenericRing.v`, `Order.v`, `Routes.v`.

---

## The typing bug (why “cannot inhabit honestly” is not “cannot prove”)

```
residual_solver_constructs_factor_open_named :=
  forall (R : RSAInstance) (Solve : residual_solver (rsa_N R) (rsa_lambda R)),
    exists f, Problem_Factor (rsa_N R) f.
```

`RSAInstance` already contains `p,q,d,λ`. `exists f` does not
mention `Solve`. Projecting `rsa_p` inhabits the Prop. That is
why every file says “do not inhabit by projecting `rsa_p`.”

`residual_solver` takes `lam` as a parameter.
`pin_miller_from_lam_factors` is a theorem. Miller-from-`λ`
also inhabits the named without touching Solve.

The **intended** sentence is: from `N` and the graph of Solve,
write a factor, with instance secrets not used as the
construction. That sentence is not what the definition says.
Until P7, honest proofs are the restricted-class theorems that
actually use Solve, with a `Not [open named]` comment stating
what they used (`d`, `d'`, `λ`, a tape, a polynomial).

`pin_p` is a global Notation, so even a Type
`forall Solve, { f | Problem_Factor pin_N f }` can still
project `pin_p`. Honesty is not fully encodable while the
factors are in the same module. Encode it in comments, in
`Not [open named]`, and in P4 (Miller’s multiple extracted
from Solve).

`rsa_problem` is exact equality `powm x e N = y`, so `y` is
already a residue. `N+1` is not a leaf. Reduced types make
that explicit. Congruence is the mathematical statement.

---

## What is still actually open (not a refuse)

After P1–P6, the remainder of the residual named is a solver
that **varies `e` with `y` and is not a homomorphism**. Nothing
in the tree shows that is impossible. Nothing constructs a
factor from it. Live target.

The unrestricted inverter (odd residual `e`, no `d` in the
construction) is the standard-model RSA ≡ factoring question.
On **this pin** the object is a finite table. Uniqueness says
a public-`e` inverter agrees with `X^d` on units, hence is an
invert-all-units function. Win B factors any such *polynomial*.
P4 is the experiment: produce that polynomial, or the local
dlogs, from Inv, then Miller. Do not call that experiment
impossible before it is run.

Strong-RSA ⇒ factor, read as “output gcd-splits,” is false
(`pin_lambda_strong_solver`). Read as `exists f`, it is the
instance-vacuity again.

On this pin every function `(ℤ/Nℤ)* → ℤ/Nℤ` is a polynomial.
“A solver is not a polynomial” is a presentation fact, not a
proof that the interpolant does not exist.

---

## Slices

Each slice: goal, why it is not leftover identities, files,
suggested names, CAS, honest-closure sentence, stop.

Suggested next CAS numbers start at 237. Do not reuse 01–236.

### P0 — Framing hygiene

**Goal.** Make the classification survive the next compaction.
Comments on the three open nameds that state the vacuity
(`RSAInstance` contains the factors; `lam` is in the residual
solver type; do not inhabit). Pointers from `README.md`
“What is left”, `THEORY.md` index, `notes/srsa-cuts.md`,
`notes/hardness.md` live-target section to this file.
Do **not** inhabit the nameds. Do **not** rewrite their types
here (that is P7).

**Why.** Compaction read “Not [open named]” and “unused” as
“cannot prove.” The harness already distinguishes the three
kinds. This slice is comments and index pointers.

**Files.** `StrongRSAPeel.v`, `Hardness.v`, `TranscriptOracle.v`
(definition comments only); this file already exists;
keep the pointers in README / THEORY / cuts / hardness in
sync if a later slice moves them.

**Stop.** Pointers exist; definition comments name the vacuity
and say unused = on-goal. No new theorem required.

---

### P1 — Uniqueness without a handed inverse

**Goal.** If `x,z` are units and `x^e ≡ z^e (mod N)` and
`gcd(e,λ)=1`, then `x ≡ z (mod N)`. Kernel: `ord(x z^{-1})`
divides `gcd(e,λ)=1`.

**Why.** `pin_unique_unit_eth_root` applies `pin_d`.
`unique_unit_eth_root_inv` applies a given `d'`. Every
“is the trapdoor map” theorem threads an inverse that the
solver did not return. The kernel argument uses `λ` via
`order_divides_lambda` / `order_divides_annihilator`, not a
constructed `d'`.

**Files.** `SrsaVaryingE.v` or `SrsaRootPoly.v`. Reuse
`order_divides_annihilator` (`Hardness.v`),
`order_divides_lambda` (`Order.v`).

**Suggested.** `unique_unit_eth_root_from_coprime_e` (general
`e` on the pin, or on `rsa_test`). Pin cases `e=3`, `e=7`,
`e=11`. Negative: `e=5` shares `λ`, cubing-style uniqueness
fails (5th powers are not a permutation).

**CAS.** Units `x ≠ z` with `x^5 ≡ z^5` (kernel nontrivial);
units with `x^7 ≡ z^7` imply `x ≡ z`.

**Honest closure.** Not the open nameds. Uniqueness is not
Miller. Uses `λ` in the order lemma, not a handed `d'`.

**Stop.** The lemma is used by P2/P3/P4/P5, or at least
`Check`ed in `Routes.v`. Print Assumptions Closed.

---

### P2 — Bézout `d'` from `(e,λ)`

**Goal.** `gcd(e,λ)=1` ⇒ exists `d'` with `e d' ≡ 1 (mod λ)`
(`Z.gcd_bezout`). Rebuild
`residual_solver_reduced_fixed_e_constructs_factor` so `d'`
is not a hypothesis. Inhabitant at `e=7` still works; Bézout
gives 23.

**Why.** The extra hyp is artificial. The residual filter
already gives `gcd(e,λ)=1`.

**Honesty.** Miller still uses `(e,λ)`, not the solver’s
`x`-values. Comment that. P4 is the slice that uses `x`.

**Files.** `SrsaVaryingE.v`. CAS 234–236 still witness the
arithmetic; add a Bézout witness (`7·23 ≡ 1 (mod 80)` from
`gcdext`) if a new file is cleaner than rewriting 234.

**Honest closure.** Not `residual_solver_constructs_factor_open_named`.
Fixed `e` plus `λ` in context.

**Stop.** The fixed-`e` theorem has no `d'` argument.
`residual_solver_reduced_pin_e_via_fixed_e` still holds
(`d' = pin_d` is what Bézout returns for `e=3`).

---

### P3 — Win B at an arbitrary residual `e`

**Goal.** A polynomial that inverts every unit at a fixed
residual `e` (not only `pin_e`) is the map `y ↦ y^{d'}` with
`e d' ≡ 1 (mod λ)`. Fermat folds are `X^{d_p}`, `X^{d_q}` for
the local inverses of **that** `e`. CRT recovers `d'` mod `λ`.
Miller from `e d'−1`.

**Why.** `invert_all_units_poly_constructs_factor` is pinned
to `pin_e` / `pin_d`. The fold theorems are already in the
shape “local inverse of the public `e`.” They need to take
`e` as a parameter, or be instantiated at 7 and 11 (inverses
23 and 51, already in `SrsaVaryingE.v`).

**Files.** `SrsaRootPoly.v` (general lemma) and/or
`SrsaVaryingE.v` (pin `e=7`, `e=11`). Nodiv / rational
wrappers can wait; one poly theorem at `e=7` is enough to
unlock P4/P5.

**CAS.** `X^{23}` inverts every unit at `e=7`; folds; Miller
from `7·23−1=160`. Same for `e=11`, `d'=51`, `M=560`.
Much of this is already 234–236; the new content is the
*polynomial* presentation at that `e`.

**Honest closure.** Not the open nameds. A solver is still
not given as a polynomial. Miller uses `d'` recovered from
the poly, which wrote the local inverses into the folds.

**Stop.** A named theorem
`invert_all_units_poly_at_e_constructs_factor` (or pin-7/11
specializations) with PA Closed. `Routes.v` Check.

---

### P4 — Recover `d` from the solver (honesty gap)

**Goal.** From a fixed-`e` residual solver or a reduced-units
inverter, produce a λ-multiple **using the solver’s `x`-values**,
then Miller. Do not pass `pin_d` / `d'` in from the instance
except as the thing being recovered.

Two constructions, both pin-finite. Either is success.

**A. Local discrete log.** `primitive_root_exists` is a theorem.
Evaluate Solve at a generator of `𝔽_p*` (residue 1..p−1, all
units of `N` on this pin because `p<q`). Brute-force
`k ∈ 0..p−2` until `g^k ≡ x (mod p)`. That is `d_p`. Same
for `q`. CRT to `d'` mod `λ`. Miller from `e d'−1`.
The solver is used. `p,q` are used as they are in every
Miller theorem on this pin.

**B. Interpolating polynomial.** The finite table
`y ↦ x(y)` agrees with the unique unit `e`-th root map
(P1). Existence of a polynomial of degree `< p` on `𝔽_p`
and `< q` on `𝔽_q`, CRT-combined, that agrees on all units.
That poly inverts every unit at `e`. Apply P3.

**Why.** This is the first time Miller’s multiple is extracted
from Solve rather than from a handed inverse. On this pin it
is a real step toward
`rsa_inverter_constructs_factor_open_named`. It is not
leftover coefficients of `K`.

**Files.** New `rocq/SrsaExtractD.v` (keep `SrsaVaryingE.v`
from growing again) or append to `SrsaVaryingE.v` if small.
`_CoqProject` sequential, before `Routes.v`.

**CAS.** For the trapdoor inhabitant, local dlog of
`36^{27} ≡ 42` at 2 or 3 recovers 27. For the `e=7`
inhabitant, dlog recovers 23. Interpolant of the 160-point
table is optional if A lands first.

**Honest closure.** Still not the unrestricted named: `e` is
fixed. Comment: Miller uses a multiple recovered from Solve
at a generator, not a hyp `d'`. If the proof still mentions
`pin_d` by `vm_compute` on the inhabitant, that is a witness,
not the theorem’s hyp.

**Stop.** A theorem
`residual_solver_reduced_fixed_e_extracts_and_factors`
(no `d'` argument; construction goes through Solve’s `x`)
and/or `rsa_inverter_reduced_units_extracts_and_factors`.
PA Closed. `Routes.v`. Do **not** mark the open named
inhabited.

---

### P5 — Homomorphic residual solver ⇒ factor

**Goal.** A residual solver whose `x`-map is a group
homomorphism (`x(y₁ y₂) ≡ x(y₁) x(y₂)` on units) constructs
a factor.

**Why.** RSA inversion *is* a homomorphism. Endomorphisms of
`(ℤ/Nℤ)* ≅ C_{p−1} × C_{q−1}` are CRT of two local power
maps.

- Matched local exponents: `y ↦ y^k` with `e k ≡ 1 (mod λ)`.
  Homomorphic plus residual-shaped `e` forces `e` constant
  mod `λ` (because `y^{k e(y)−1} ≡ 1` for all units). That
  is the fixed-`e` / `e`-cong class. Apply P3/P4.
- Mismatched locals: CRT binomial; coefficients split
  (`pin_root_ca_splits`).

This is Win B in group language, not “given as a polynomial.”

**Files.** `SrsaVaryingE.v` or `SrsaExtractD.v`. Reuse
`invert_all_units_local_p` / `_q`,
`pin_crt_binomial_*`.

**CAS.** Hom of the trapdoor map; a mismatched local pair
(`d_p` on p-side, `d_q` on q-side) splits by gcd of the
binomial coefficients; a non-homomorphic leftover table
(e.g. cube root on some units, 7th root on others) is a
negative for this class, not a refuse of the named.

**Honest closure.** Not the open nameds. Restriction is
homomorphism. Varying-`e` non-hom solvers remain open.

**Stop.** Named theorem plus the “`e` constant mod `λ`”
lemma. PA Closed. `Routes.v`.

---

### P6 — Lattice arrows and the annihilator-`e` class

**Goal.** Write the arrows that already exist as theorems,
and package one more class.

Already have, make explicit:

- Public-`e` inverter ⇒ residual solver (`inverter_as_residual`).
- Strong-RSA solver returning public `e` ⇒ inverter
  (`strong_solver_as_inverter`).
- Therefore: residual-solver ⇒ factor, on this pin, would
  imply inverter ⇒ factor. Residual named is the stronger
  claim.

New class:

- Strong-RSA (or residual-filter-dropped) solver whose
  output satisfies `λ | e−1`: Miller-from-`(e−1)`.
  Residual *excludes* this leaf. `λ+1` is the inhabitant;
  `e−1 = λ`. Prime `e = kλ+1` is the same trick; `e−1`
  still Millers. Package:
  `strong_rsa_solver_e_minus_1_millers` under the hyp
  `λ | e−1` (or `powm g (e−1) N = 1` for a unit `g` of
  order `λ`, so the test can be stated from outputs plus
  a generator).

**Honesty.** If the hyp is `λ | e−1`, Miller uses `e−1`
from the solver and `λ` to test. If the hyp is
“`g^{e−1} ≡ 1` for a max-order unit,” the generator is
extra. Neither inhabits the unrestricted named: the
λ-trick solver *does* miller from `e−1`, and that is
the point of the class. Residual solvers are outside
the class by construction.

**Do not** prove `~ forall Solve, exists f`.

**CAS.** `e=81`, `e−1=80` Millers; `e=241` if used;
`e=3`, `e−1=2` does not; `e=7`, `e−1=4` does not
(already `pin_e7_minus_pin_e_does_not_miller`).

**Stop.** The implication lattice is `Check`ed in
`Routes.v`. The `e−1` class has a theorem and a residual
negative. PA Closed.

---

### P7 — Re-type / re-comment the live targets

**Goal.** Stop the nameds from being instance-vacuous,
without accidentally inhabiting them.

**Do not** silently change the existing Prop so a later
agent “closes” it by projecting `rsa_p`.

Options (pick one, do not do both in one turn):

1. **Comment-only.** On each of the three definitions,
   state: `exists f` ignores Solve; `RSAInstance` contains
   the factors; `lam` is in the residual Type; inhabiting
   by `rsa_p` or miller-from-`λ` is forbidden; the intended
   sentence is extraction from the graph. P0 overlaps;
   this option is P0 plus Routes comments.

2. **Add a constructive Type, keep the old Prop unused.**
   e.g. `residual_solver_extracts_factor_open_named` as a
   `Type` (`forall Solve, { f | Problem_Factor pin_N f }`)
   with the same unused-means-unproved discipline. Comment
   that `pin_p` is still in scope so honesty remains a
   comment. `Routes.v` Checks the new name. Do not inhabit.

3. **Quantify over `N` without `RSAInstance`.** Residual
   filter without putting `λ` in the Type needs a λ-free
   approximation (prime `e` / BP97, or a public challenge
   space). Prime `e = kλ+1` is still the λ-trick; P6
   covers miller-from-`(e−1)`. A λ-free residual is a
   new definition; do not pretend it is the old named.

**Stop.** The vacuity is visible from `Routes.v` comments
and `NAMED_SKIPS.md`. No green “Closed” of an open named
by projection.

---

### P8 — Stale refuses that are deferred algebra

**Goal.** Stop unused `*_named` that are classical algebra
from being read as “cannot prove.” Either prove a slice or
retarget the definition to `*_open_named` (live, not refuse).

**Not in this slice:** `NamedRefuse` constructors (ROM, PPT,
NFS, LLL development, AM09-as-standard-model, OAEP/PSS,
HVZK, …). Those stay.

| Named | Stated blocker | Actual state | Work |
|---|---|---|---|
| `pratt_complete_named` | “Needs a primitive root in every `𝔽_p*`” | `primitive_root_exists` is a theorem. Soundness and 2-primary duality with Miller are proved. Completeness is: factor `p−1` and recurse. | Prove completeness, or rename to `pratt_complete_open_named` and fix the comment. Stay unused as a hyp. |
| `orders_generate_lambda_named` | “Sampling-completeness / density” | `exists_unit_order_lambda` already constructs a unit of order `λ` for general distinct primes. The named is a template over a predicate `ks`. | Instantiate for a concrete `ks`, or retarget to open. Do not take as hyp. |
| `compose_preserves_disc_named` | Remaining two-form branch | Inverse pairs, unit leading coeff, ambiguous self-composition are theorems. | Prove the remaining branch, or retarget to open. |
| `compose_assoc_named` | Associativity except `{id,f,f⁻¹}` | Identity laws on that triple are theorems. | Same. |
| `compose_left_compat_named` | Blocks a class-group wall lemma | Deferred Dirichlet algebra. | Same. |
| `eval_pair_needs_integer_named` | This pairing takes `k` in the clear | Correct *scope*. `mu3N_det_*` is a different pairing and uses the factors. | Leave as named (scope), do not promote to `NamedRefuse`. |

**Honesty.** Proving Pratt completeness or Dirichlet
composition does **not** discharge the three RSA nameds.
`Not [rsa_inverter_constructs_factor_open_named]` etc.

**Stop.** Either a Closed completeness/composition theorem,
or the definition is `*_open_named` and `named-skips`
lists it under open, not refuse. Comment matches reality
(`primitive_root_exists` is not still a blocker).

Priority inside P8: Pratt comment fix / retarget first
(blocker is already gone), then `exists_unit_order_lambda`
vs the orders named, then composition if touching
`BinForms.v` anyway.

---

## Suggested pick order

Default if the user says “go” without a slice id:

1. **P1** then **P2** then **P3** then **P4** — uniqueness,
   drop the fake hyp, Win B at general residual `e`, extract
   `d` from Solve. That is the honesty gap on the inverter
   and fixed-`e` residual classes.
2. **P5** — homomorphic packaging, once P3 exists.
3. **P6** — lattice + annihilator-`e`, cheap once P2/P4 exist.
4. **P7** when touching the nameds anyway; **P0** is comments
   and can ride with any slice.
5. **P8** when not on the RSA nameds; it is real algebra and
   prevents the next compaction from re-refusing Pratt.

If the user names a slice, do that slice, not this default.

---

## Death conditions (stop the slice, do not “complete” it)

- The proof millers from `pin_d` / `rsa_d` / `rsa_lambda`
  while the theorem’s comment claims the solver constructed
  the multiple. Fix the comment or the construction (P4).
- The proof inhabits an `*_open_named`. Revert.
- The proof takes an `*_named` as a hypothesis. Revert.
- CAS `gp` exits 0 with a syntax error (the cas-gate
  footgun). Fail the slice.
- Stale `.vo` after `Pin.v` edits. Rebuild from Pin.
- A new C-class that already contains `d` or `λ` as a hyp
  and Millers from it, without extracting from Solve, is
  **P2-shaped at best**. Do not sell it as P4 or as the
  open named.
- Leftover kernel `K`, Fermat-fold coefficients, related-`y`
  identities already in `SrsaExtra.v` / `DozenInroads.v`:
  not a slice. Do not resume.

---

## After each landed slice

1. `Not [the three open nameds]` on new subsections unless
   the slice actually inhabits one (it should not, before
   a user decision that P4 on this pin *is* the inverter
   named — it is not; `e` is still fixed).
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

You are in the unknown-order Strong RSA campaign. The
C-class method (restrict the solver until it already
contains `d` or `λ`, Miller, stop) ran out of *obvious*
restrictions. The algebra did not run out. The three
`*_open_named` are live. Do not mark nearby algebra as
refused because it is unproved. Next work is the status
table at the top of this file, in the pick order above,
under the hard constraints above. Pin 187. CAS 236+ as
landed. Do not inhabit the nameds. Do not resume kernel
folds. Do not treat GRA as standard-model hardness.
