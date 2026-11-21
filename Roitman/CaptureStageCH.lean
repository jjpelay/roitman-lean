import Roitman.CaptureStage
import Roitman.StageCH

namespace Roitman

theorem captureStageCH
    (d : ℕ → ℕ) (G : Set ℕ) (previous : ℕ → Set ℕ)
    (ds : ℕ → ℕ → ℕ) (old : ℕ → Set ℕ) (X : Set (Finset ℕ))
    (hds : ∀ r n, n ≤ ds r n)
    (noCover : ∀ n b, ¬ K d (G ∩ exclusions previous n b))
    (escape : ∀ n b, ∃ i, i ∉ exclusions previous n b)
    (oldGaps : ∀ r, {j | Disjoint (old r) (interval (ds r) j)}.Infinite)
    (positive : ∀ n b, ∃ t ∈ X, t.Nonempty ∧
      ∀ i ∈ t, i ∉ exclusions previous n b) :
    ∃ a : Set ℕ,
      a.Infinite ∧
      (∀ k, (a ∩ previous k).Finite) ∧
      (∀ x, K d x → x ⊆ G → (x ∩ a).Infinite) ∧
      (∀ r, {j | Disjoint (old r ∪ a) (interval (ds r) j)}.Infinite) ∧
      {t : Finset ℕ | t ∈ X ∧ (↑t : Set ℕ) ⊆ a}.Infinite := by
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
  have blocksCH : ∀ n b : ℕ, ∃ s : Finset ℕ,
      s.Nonempty ∧ (∀ i ∈ s, b ≤ i) ∧
      (∀ k ≤ n, ∀ i ∈ s, i ∉ previous k) ∧
      (∀ x ∈ targets, ∃ i ∈ s, i ∈ x) ∧
      (∃ t ∈ X, t.Nonempty ∧ t ⊆ s) := by
    intro n b
    obtain ⟨s, hs, hslow, hsavoid, hshit⟩ := blocks n b
    obtain ⟨t, htX, htne, htavoid⟩ := positive n b
    refine ⟨s ∪ t, hs.mono Finset.subset_union_left, ?_, ?_, ?_,
      t, htX, htne, Finset.subset_union_right⟩
    · intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact hslow i hi
      · exact Nat.le_of_not_gt (fun h => htavoid i hi (Or.inl h))
    · intro k hk i hi hic
      rcases Finset.mem_union.mp hi with hi | hi
      · exact hsavoid k hk i hi hic
      · exact htavoid i hi (Or.inr ⟨k, hk, hic⟩)
    · intro x hx
      obtain ⟨i, his, hix⟩ := hshit x hx
      exact ⟨i, Finset.mem_union_left t his, hix⟩
  have lower : ∀ r j i, i ∈ intervals r j → j ≤ i := by
    intro r j i hi
    have hi' := (interval_finite (ds r) j).mem_toFinset.mp hi
    exact (le_h (hds r) j).trans hi'.1
  have localGaps : ∀ r M : ℕ, ∃ j : ℕ,
      M ≤ j ∧ j ∈ allowed r ∧ ∀ i ∈ intervals r j, M ≤ i := by
    intro r M
    obtain ⟨j, hj, hMj⟩ := (oldGaps r).exists_gt M
    exact ⟨j, hMj.le, hj, fun i hi => hMj.le.trans (lower r j i hi)⟩
  obtain ⟨a, ha, had, hcapture, hpreserve, hX⟩ :=
    finiteBlocksStageCH previous targets X intervals allowed
      (fun n => (Nat.unpair n).1) unpairSchedule_fair blocksCH localGaps
  refine ⟨a, ha, had, ?_, ?_, hX⟩
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
