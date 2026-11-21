# 𝔡 = ω₁ implies 𝔞 = ω₁: a Lean 4 formalization

Lean 4 / Mathlib formalization of the main theorem of

> José de Jesús Pelayo Gómez, *𝔡 = ω₁ implies 𝔞 = ω₁*, [arXiv:2610.00639](https://arxiv.org/abs/2610.00639).

The theorem settles, in ZFC, a question of Roitman from the 1970s: if the dominating number 𝔡 is ℵ₁, then the
almost-disjointness number 𝔞 is ℵ₁.

## How this formalization came about

The proofs were written first, on paper; this Lean formalization came afterwards, as a check of the finished
manuscripts. It was not used to discover the proof.

There were two written versions of the argument, and both were formalized:

- **Recipe B** (`Roitman/RecetaB/`) is **the paper exactly as posted on arXiv** ([arXiv:2610.00639](https://arxiv.org/abs/2610.00639)).
  Its construction uses reservation towers, and the lemma and theorem numbers in its comments are those of the
  arXiv version.
- **The first construction** (`Roitman/`, top level) is a **preliminary version that was never published**. It
  proves the same theorem with a gap invariant and a counting lemma instead.

So the main theorem is checked twice, through two different constructions of the MAD family. Both share the basic
definitions (`IsMAD`, `DominatingSet`, the cardinal characteristics) and the domination lemmas.

## Main statements

```lean
-- Roitman/RecetaB/Main.lean  (and Roitman.d_eq_aleph_one_implies_a_eq_aleph_one in Roitman/Main.lean)
theorem Roitman.RecetaB.d_eq_aleph_one_implies_a_eq_aleph_one_recetaB
    (hd : IsDominatingNumber (Cardinal.aleph 1)) :
    IsAlmostDisjointnessNumber (Cardinal.aleph 1)

-- Roitman/RecetaB/Separable.lean  (Theorem 5.1 of the preprint; no CH)
theorem Roitman.RecetaB.d_eq_aleph_one_implies_almostStronglySeparable_MAD
    (hd : IsDominatingNumber (Cardinal.aleph 1)) :
    ∃ A : I → Set ℕ, MADFamily A ∧
      Cardinal.mk (Set.range A) = Cardinal.aleph 1 ∧ AlmostStronglySeparable A

-- Roitman/Corollaries.lean
theorem Roitman.a_le_d_of_continuum_le_aleph_two {a d : Cardinal}
    (ha : IsAlmostDisjointnessNumber a) (hd : IsDominatingNumber d)
    (hc : Cardinal.continuum ≤ Cardinal.aleph 2) : a ≤ d
```

Also formalized: the version that starts from a concrete dominating family of size ℵ₁ and returns a MAD family of
size ℵ₁ (`dominating_aleph_one_implies_mad_aleph_one`), the lower bounds ℵ₂ ≤ 𝔡 and ℵ₃ ≤ 𝔞 ≤ 𝔠 for any model of
𝔡 < 𝔞 (`strict_d_lt_a_lower_bounds`), and the Shelah–Steprāns property of almost strongly separable families.

## Definitions

The statements use the standard notions, defined directly in this repository:

| Lean | Meaning |
|---|---|
| `IsMAD F` (`Maximality.lean`) | `F` is an infinite family of infinite subsets of ℕ, pairwise with finite intersection, and every infinite `x ⊆ ℕ` meets some member of `F` in an infinite set |
| `DominatingSet F` (`Maximality.lean`) | every `f : ℕ → ℕ` is eventually bounded by some `g ∈ F` |
| `IsDominatingNumber κ` (`CardinalBounds.lean`) | some dominating set has cardinality `κ`, and every dominating set has cardinality at least `κ` |
| `IsAlmostDisjointnessNumber κ` (`CardinalBounds.lean`) | some MAD family has cardinality `κ`, and every MAD family has cardinality at least `κ` |

Uniqueness of these least values is also proved (`IsDominatingNumber_unique`, `IsAlmostDisjointnessNumber_unique`).
The construction of the MAD family is proved, not assumed: it is a well-founded recursion of length ω₁.

## Axioms

There is no `sorry`, no `admit` and no new axiom. `Audit.lean` and `AuditRecetaB.lean` print the axioms each final
result depends on; all of them use only Lean's standard axioms:

```
'Roitman.RecetaB.d_eq_aleph_one_implies_a_eq_aleph_one_recetaB' depends on axioms: [propext, Classical.choice, Quot.sound]
'Roitman.d_eq_aleph_one_implies_a_eq_aleph_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The continuous-integration workflow (`.github/workflows/build.yml`) builds the project from scratch and fails if any
audited result depends on `sorryAx` or any other unexpected axiom.

## Scope

This formalizes the ZFC theorem and its combinatorial consequences. It does **not** formalize forcing, preservation
of the MAD family in outer models, or the consistency results cited in the paper, nor the implications from the
literature (Shelah–Steprāns to tight, Cohen-indestructibility).

A few presentation choices differ from the paper while proving the same statements: the bookkeeping map onto stages
of ω₁ is an injection with spare stages, rather than the exact lexicographic bijection, and in recipe B the dominating
family is replaced by the maximum of its normalization and a scale built by recursion, rather than by reindexing it.

## Building

Requirements: [elan](https://lean-lang.org/install/) and Git. The Lean version is pinned in `lean-toolchain`
(`leanprover/lean4:v4.35.0-rc3`) and Mathlib is pinned to commit `b63f6e8a68d220e3b3bc4f3792bb53650d375f24`.

```sh
lake exe cache get          # download prebuilt Mathlib
lake build                  # compile this project
lake env lean Audit.lean    # axiom audit, first construction
lake env lean AuditRecetaB.lean   # axiom audit, recipe B
```

## License

Apache License 2.0, the same as Mathlib. See `LICENSE`.
