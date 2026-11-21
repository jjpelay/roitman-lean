import Roitman.ConstructionSupport

/-!
# Recipe B: the reservation invariant

Formalization of the construction in arXiv:2610.00639, where the
gap invariant and the counting lemma of the earlier draft of arXiv:2610.00639 (first construction) are replaced by a
tower of reserved intervals and whole blocks `G ∩ I_j`.

The files in `Roitman/RecetaB` are additions. They reuse the definitions of the
original formalization (`K`, `interval`, `traceClass`, `task`, `gamma`, the
recursion principle and the domination lemmas) and do not modify any original
file.
-/

noncomputable section
namespace Roitman.RecetaB
open Roitman Bookkeeping

/-- The value chosen at stage `ξ`: the new member `a_ξ`, and for each `α` the
set `R^α_{ξ+1}` of indices of the intervals of `d α` reserved after stage `ξ`. -/
abbrev StageValue := Set ℕ × (I → Set ℕ)

/-- The members `a_η` of the family. -/
def members (f : I → StageValue) : I → Set ℕ := fun η => (f η).1

/-- The class set `G_{α,β}` of the stage `ξ`, with `(α, β) = task ξ`. -/
def stageClass (d : I → ℕ → ℕ) (f : I → StageValue) (ξ : I) : Set ℕ :=
  traceClass d (members f) (task ξ).1 (task ξ).2

/-- Everything certified at stage `ξ` of recipe B:
1. `a_ξ` is infinite;
2. it is almost disjoint from every earlier member;
3. every reservation `R^α_{ξ+1}` with `α ≤ ξ` is infinite;
4. the reservations form a `⊆*`-decreasing tower;
5. `a_ξ` misses every reserved interval `I^α_j`, `j ∈ R^α_{ξ+1}`;
6. if `G_{α,β}` meets all but finitely many intervals `I^α_j`, then `a_ξ`
   contains `G_{α,β} ∩ I^α_j` for infinitely many `j`. -/
def GoodB (d : I → ℕ → ℕ) (ξ : I) (f : I → StageValue) : Prop :=
  ((f ξ).1).Infinite ∧
  (∀ η, η < ξ → ((f ξ).1 ∩ (f η).1).Finite) ∧
  (∀ α, α ≤ ξ → ((f ξ).2 α).Infinite) ∧
  (∀ α η, α ≤ η → η < ξ → ((f ξ).2 α \ (f η).2 α).Finite) ∧
  (∀ α, α ≤ ξ → ∀ j ∈ (f ξ).2 α, Disjoint (f ξ).1 (interval (d α) j)) ∧
  ({j | ¬ (stageClass d f ξ ∩ interval (d (task ξ).1) j).Nonempty}.Finite →
    {j | stageClass d f ξ ∩ interval (d (task ξ).1) j ⊆ (f ξ).1}.Infinite)

theorem stageClass_congr {d : I → ℕ → ℕ} {f g : I → StageValue} {ξ : I}
    (h : ∀ η, η < ξ → f η = g η) : stageClass d f ξ = stageClass d g ξ := by
  unfold stageClass
  apply traceClass_congr
  intro η hη
  simp only [members, h η (lt_of_lt_of_le hη (task_fst_le ξ))]

private theorem goodB_transfer (d : I → ℕ → ℕ) (ξ : I) (f g : I → StageValue)
    (h : ∀ η, η ≤ ξ → f η = g η) (hf : GoodB d ξ f) : GoodB d ξ g := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf
  have hξ := h ξ le_rfl
  refine ⟨hξ ▸ h1, ?_, hξ ▸ h3, ?_, hξ ▸ h5, ?_⟩
  · intro η hη
    rw [← hξ, ← h η hη.le]
    exact h2 η hη
  · intro α η hαη hη
    rw [← hξ, ← h η hη.le]
    exact h4 α η hαη hη
  · rw [← stageClass_congr (fun η hη => h η hη.le), ← hξ]
    exact h6

theorem goodB_locality (d : I → ℕ → ℕ) (ξ : I) (f g : I → StageValue)
    (h : ∀ η, η ≤ ξ → f η = g η) : GoodB d ξ f ↔ GoodB d ξ g :=
  ⟨goodB_transfer d ξ f g h, goodB_transfer d ξ g f (fun η hη => (h η hη).symm)⟩

end Roitman.RecetaB
