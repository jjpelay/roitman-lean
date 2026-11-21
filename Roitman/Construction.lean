import Roitman.ConstructionSupport
import Roitman.Recursion
import Roitman.Extension

noncomputable section
namespace Roitman
open Bookkeeping

/-- A bridge to transfinite recursion. Its extension premise must be discharged
by the finite-stage construction before this yields the construction lemma. -/
theorem construction_of_extension (d : I → ℕ → ℕ)
    (extend : ∀ ξ A, (∀ η, η < ξ → GoodAt d task η A) →
      ∃ a, GoodAt d task ξ (Function.update A ξ a)) :
    ∃ A, ∀ ξ, GoodAt d task ξ A := by
  apply local_recursion (GoodAt d task)
  · exact goodAt_locality d task task_fst_le
  · exact extend

/-- The construction lemma: no domination hypothesis is needed for the
almost-disjoint recursion and its simultaneous capture requirements. -/
theorem exists_good_family (d : I → ℕ → ℕ) (hd : ∀ α n, n ≤ d α n) :
    ∃ A, ∀ ξ, GoodAt d task ξ A :=
  construction_of_extension d (goodAt_extension d hd)

/-- The capture clause at the stage assigned to an arbitrary pair. -/
theorem good_capture {d : I → ℕ → ℕ} {A : I → Set ℕ}
    (hA : ∀ ξ, GoodAt d task ξ A) (α β : I) {x : Set ℕ}
    (hx : K (d α) x) (hsub : x ⊆ traceClass d A α β) :
    (x ∩ A (gamma (α, β))).Infinite := by
  have hc := (hA (gamma (α, β))).2.2.2
  rw [task_gamma] at hc
  exact hc x hx hsub

end Roitman
