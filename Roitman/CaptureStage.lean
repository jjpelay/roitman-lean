import Roitman.Basic
import Roitman.Stage

namespace Roitman

/-- The finite exclusions at step `n` with lower cutoff `b`. -/
def exclusions (previous : ℕ → Set ℕ) (n b : ℕ) : Set ℕ :=
  {i | i < b ∨ ∃ k ≤ n, i ∈ previous k}

/-- The manuscript's single-stage construction.  `noCover` and `escape` are
local consequences of the gap invariant (the latter using alpha = 0).
The output preserves every enumerated old gap requirement. -/
theorem captureStage
    (d : ℕ → ℕ) (G : Set ℕ) (previous : ℕ → Set ℕ)
    (ds : ℕ → ℕ → ℕ) (old : ℕ → Set ℕ)
    (hds : ∀ r n, n ≤ ds r n)
    (noCover : ∀ n b, ¬ K d (G ∩ exclusions previous n b))
    (escape : ∀ n b, ∃ i, i ∉ exclusions previous n b)
    (oldGaps : ∀ r, {j | Disjoint (old r) (interval (ds r) j)}.Infinite) :
    ∃ a : Set ℕ,
      a.Infinite ∧
      (∀ k, (a ∩ previous k).Finite) ∧
      (∀ x, K d x → x ⊆ G → (x ∩ a).Infinite) ∧
      (∀ r, {j | Disjoint (old r ∪ a) (interval (ds r) j)}.Infinite) := by
  classical
  let targets : Set (Set ℕ) := {x | K d x ∧ x ⊆ G}
  let intervals (r j : ℕ) := (interval_finite (ds r) j).toFinset
  let allowed (r : ℕ) := {j | Disjoint (old r) (interval (ds r) j)}
  have blocks : ∀ n b : ℕ, ∃ s : Finset ℕ,
      s.Nonempty ∧ (∀ i ∈ s, b ≤ i) ∧
      (∀ k ≤ n, ∀ i ∈ s, i ∉ previous k) ∧
      (∀ x ∈ targets, ∃ i ∈ s, i ∈ x) := by
    intro n b
    by_cases hG : K d G
    · obtain ⟨m, _, hf, hne, hhit⟩ := finite_hitting hG (noCover n b)
      refine ⟨hf.toFinset, ?_, ?_, ?_, ?_⟩
      · obtain ⟨i, hi⟩ := hne
        exact ⟨i, hf.mem_toFinset.mpr hi⟩
      · intro i hi
        have hiE := (hf.mem_toFinset.mp hi).1.2
        exact Nat.le_of_not_gt (fun h => hiE (Or.inl h))
      · intro k hk i hi hip
        have hiE := (hf.mem_toFinset.mp hi).1.2
        exact hiE (Or.inr ⟨k, hk, hip⟩)
      · intro x hx
        obtain ⟨i, hix, his⟩ := hhit x hx.1 hx.2
        exact ⟨i, hf.mem_toFinset.mpr his, hix⟩
    · obtain ⟨i, hi⟩ := escape n b
      refine ⟨{i}, Finset.singleton_nonempty i, ?_, ?_, ?_⟩
      · intro z hz
        have hzi : z = i := Finset.mem_singleton.mp hz
        subst z
        exact Nat.le_of_not_gt (fun h => hi (Or.inl h))
      · intro k hk z hz hzp
        have hzi : z = i := Finset.mem_singleton.mp hz
        subst z
        exact hi (Or.inr ⟨k, hk, hzp⟩)
      · intro x hx
        exact False.elim (hG (K_mono hx.1 hx.2))
  have lower : ∀ r j i, i ∈ intervals r j → j ≤ i := by
    intro r j i hi
    have hi' := (interval_finite (ds r) j).mem_toFinset.mp hi
    exact (le_h (hds r) j).trans hi'.1
  obtain ⟨a, ha, had, hcapture, hpreserve⟩ :=
    finiteBlocksStage_of_infinite_gaps previous targets intervals allowed blocks oldGaps lower
  refine ⟨a, ha, had, ?_, ?_⟩
  · intro x hx hxG
    exact hcapture x ⟨hx, hxG⟩
  · intro r
    apply (hpreserve r).mono
    intro j hj
    apply Set.disjoint_left.mpr
    intro i hi hii
    rcases hi with hio | hia
    · exact Set.disjoint_left.mp hj.1 hio hii
    · exact hj.2 i ((interval_finite (ds r) j).mem_toFinset.mpr hii) hia
end Roitman
