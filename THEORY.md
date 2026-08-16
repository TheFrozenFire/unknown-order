# Groups of unknown order (working document)

This is the evolving account of the *generalizable* structure behind computational problems in
groups whose order is not given to the algorithm. It grows as we add problems. Right now it is a
frame: the first worked object will be the RSA problem on `(ℤ/Nℤ)*`.

Everything asserted here will be machine-checked; theorem names will point at `rocq-proofs/`
(reusable) and `rocq/RSA.v` (instantiation). Until a claim has a theorem and a CAS witness, it
does not belong below as a fact.

## 1. The domain, minimally

A **group of unknown order** is a group `G` in which the group operation is efficient, but `|G|`
(and typically a factorization of `|G|`) is not part of the public input. Hardness assumptions in
this setting — RSA, strong RSA, adaptive root, order, low-order, … — are statements about
algorithms that see `G` and some extra elements, and must produce a root, an order, or a
factorization.

`(ℤ/Nℤ)*` with `N = pq` is the smallest example that already contains the whole skeleton: a
public exponent `e`, a private exponent `d` whose existence is equivalent to invertibility of `e`
modulo `λ(N)` (or `φ(N)`), and a family of algorithms that, given `(N, e, d)`, recover `{p, q}`.

## 2. First object: the RSA problem, `d`, and factoring from `(e, d)`

To be filled from the analysis seed. Intended contents, not yet claimed:

- The RSA instance: primes `p, q`, modulus `N = pq`, public exponent `e` coprime to `λ(N)`,
  private exponent `d` with `ed ≡ 1 (mod λ(N))` (and the `φ(N)` variant, with an honest statement
  of which inverse is which).
- The RSA *problem*: given `(N, e, y)`, find `x` with `x^e ≡ y (mod N)`.
- The algorithms that, given `(N, e, d)`, output `{p, q}` — some deterministic, some randomized —
  each as a Gallina definition with a precise success statement.

No algorithm is named as "the" algorithm until the seed conversation has been read.

## 3. Honest scope

This document does not yet assert any theorem. The scaffold compiles; the mathematics is not
formalized.
