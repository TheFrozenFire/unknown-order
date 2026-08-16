From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * RSA: the RSA problem in [(Z/NZ)*]

    Scaffold. Definitions and algorithms land after the analysis seed.

    Intended contents (not yet defined):

    - An RSA instance: primes [p], [q], modulus [N = p * q], public exponent [e]
      coprime to [λ(N)] (and the [φ(N)] variant), private exponent [d] with
      [e * d ≡ 1 (mod λ(N))].
    - The RSA *problem*: given [(N, e, y)], find [x] such that [x^e ≡ y (mod N)].
    - The algorithms that, given [(N, e, d)], recover [{p, q}] — some
      deterministic, some randomized — each as a Gallina definition with a
      precise success statement.

    Cross-confirmation: every headline theorem here will have a PARI/GP witness
    in [cas/NN_*.gp]. Reusable number-theoretic facts (gcd, totient, Carmichael,
    splitting) that a second unknown-order problem would also need belong in
    [rocq-proofs], not here. *)
