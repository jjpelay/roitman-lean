import Roitman.ConstructionDefs

noncomputable section
namespace Roitman
open Bookkeeping

theorem earlier_congr {A B : I → Set ℕ} {α : I}
    (h : ∀ η, η < α → A η = B η) : earlier A α = earlier B α := by
  funext k
  unfold earlier
  cases he : enumEarlier α k with
  | none => rfl
  | some η => exact h η (enumEarlier_lt he)

theorem traceClass_congr {d : I → ℕ → ℕ} {A B : I → Set ℕ} {α β : I}
    (h : ∀ η, η < α → A η = B η) :
    traceClass d A α β = traceClass d B α β := by
  unfold traceClass
  rw [earlier_congr h]

theorem gapIndices_congr {d : I → ℕ → ℕ} {A B : I → Set ℕ}
    {α : I} {u : Finset I} (h : ∀ η ∈ u, A η = B η) :
    gapIndices d A α u = gapIndices d B α u := by
  ext j
  simp only [gapIndices, Set.mem_setOf_eq]
  constructor <;> intro hj η hη
  · rw [← h η hη]
    exact hj η hη
  · rw [h η hη]
    exact hj η hη

private theorem goodAt_transfer (d : I → ℕ → ℕ) (task : I → I × I)
    (task_le : ∀ ξ, (task ξ).1 ≤ ξ) (ξ : I) (A B : I → Set ℕ)
    (h : ∀ η, η ≤ ξ → A η = B η) (hA : GoodAt d task ξ A) :
    GoodAt d task ξ B := by
  obtain ⟨hinf, had, hgap, hcapture⟩ := hA
  have hξ := h ξ le_rfl
  refine ⟨hξ ▸ hinf, ?_, ?_, ?_⟩
  · intro η hη
    rw [← hξ, ← h η hη.le]
    exact had η hη
  · intro α hα u hu
    rw [← gapIndices_congr (fun η hη => h η (hu η hη).2)]
    exact hgap α hα u hu
  · intro x hx hxsub
    rw [← hξ]
    apply hcapture x hx
    rw [traceClass_congr (fun η hη => h η (hη.le.trans (task_le ξ)))]
    exact hxsub

theorem goodAt_locality (d : I → ℕ → ℕ) (task : I → I × I)
    (task_le : ∀ ξ, (task ξ).1 ≤ ξ) (ξ : I) (A B : I → Set ℕ)
    (h : ∀ η, η ≤ ξ → A η = B η) :
    GoodAt d task ξ A ↔ GoodAt d task ξ B :=
  ⟨goodAt_transfer d task task_le ξ A B h,
    goodAt_transfer d task task_le ξ B A (fun η hη => (h η hη).symm)⟩

/-- At a stage, every finite earlier gap requirement has already been
certified at its largest index. This also handles limit stages. -/
theorem gaps_before {d : I → ℕ → ℕ} {task : I → I × I}
    {ξ : I} {A : I → Set ℕ}
    (hprev : ∀ η, η < ξ → GoodAt d task η A)
    (α : I) (u : Finset I) (hu : ∀ η ∈ u, α ≤ η ∧ η < ξ) :
    (gapIndices d A α u).Infinite := by
  classical
  by_cases hne : u.Nonempty
  · have hm := hu (u.max' hne) (Finset.max'_mem u hne)
    exact (hprev (u.max' hne) hm.2).2.2.1 α hm.1 u
      (fun η hη => ⟨(hu η hη).1, Finset.le_max' u η hη⟩)
  · have he : u = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simpa [he, gapIndices] using (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)

end Roitman
