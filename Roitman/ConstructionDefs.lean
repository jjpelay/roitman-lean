import Roitman.Basic
import Roitman.Bookkeeping

noncomputable section
namespace Roitman
open Bookkeeping

def earlier (A : I → Set ℕ) (α : I) (k : ℕ) : Set ℕ :=
  (enumEarlier α k).elim ∅ A

def traceClass (d : I → ℕ → ℕ) (A : I → Set ℕ) (α β : I) : Set ℕ :=
  traceSet (earlier A α) (d β)

def gapIndices (d : I → ℕ → ℕ) (A : I → Set ℕ) (α : I) (u : Finset I) : Set ℕ :=
  {j | ∀ η ∈ u, Disjoint (A η) (interval (d α) j)}

/-- All invariants newly certified at an individual stage. -/
def GoodAt (d : I → ℕ → ℕ) (task : I → I × I) (ξ : I) (A : I → Set ℕ) : Prop :=
  (A ξ).Infinite ∧
  (∀ η, η < ξ → (A ξ ∩ A η).Finite) ∧
  (∀ α, α ≤ ξ → ∀ u : Finset I,
    (∀ η ∈ u, α ≤ η ∧ η ≤ ξ) → (gapIndices d A α u).Infinite) ∧
  (∀ x, K (d (task ξ).1) x → x ⊆ traceClass d A (task ξ).1 (task ξ).2 →
    (x ∩ A ξ).Infinite)

end Roitman
