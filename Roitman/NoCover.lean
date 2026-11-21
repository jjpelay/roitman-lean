import Roitman.Basic

namespace Roitman

/-- Adding a finite set does not destroy infinitely many omitted intervals. -/
theorem gaps_finite_union {d : ℕ → ℕ} (hd : ∀ n, n ≤ d n)
    {z B : Set ℕ} (hB : B.Finite)
    (hz : {j | Disjoint z (interval d j)}.Infinite) :
    {j | Disjoint (B ∪ z) (interval d j)}.Infinite := by
  obtain ⟨L, hL⟩ := hB.bddAbove
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨j, hj, hjbig⟩ := hz.exists_gt (max N L)
  refine ⟨j, ?_, lt_of_le_of_lt (le_max_left _ _) hjbig⟩
  apply Set.disjoint_left.mpr
  intro i hi hii
  rcases hi with hi | hi
  · have hiL := hL hi
    have hjh := le_h hd j
    have hhi := hii.1
    have hLj : L < j := lt_of_le_of_lt (le_max_right _ _) hjbig
    omega
  · exact Set.disjoint_left.mp hj hi hii

/-- The no-cover lemma in the exact finite-head/tail form used at a stage. -/
theorem noCover {d : ℕ → ℕ} (hd : ∀ n, n ≤ d n)
    {G E early late : Set ℕ} (hE : E ⊆ early ∪ late)
    (hfinite : (G ∩ early).Finite)
    (hgaps : {j | Disjoint late (interval d j)}.Infinite) :
    ¬ K d (G ∩ E) := by
  have gaps := gaps_finite_union hd hfinite hgaps
  obtain ⟨j, hj⟩ := gaps.nonempty
  apply not_K_of_missed_interval (j := j)
  apply Set.disjoint_left.mpr
  intro i hi hii
  apply Set.disjoint_left.mp hj _ hii
  rcases hE hi.2 with he | hl
  · exact Or.inl ⟨hi.1, he⟩
  · exact Or.inr hl

end Roitman
