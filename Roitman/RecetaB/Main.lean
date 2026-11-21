import Roitman.RecetaB.Extension
import Roitman.Recursion
import Roitman.Maximality
import Roitman.CardinalBounds

/-!
# Recipe B: construction lemma, maximality and the main theorem

The construction lemma of arXiv:2610.00639 (Lemma 3.1), proved with
the reservation towers instead of the gap invariant, and the title theorem
obtained from it with the same domination lemmas as the original
formalization.
-/

noncomputable section
namespace Roitman.RecetaB
open Roitman Bookkeeping

/-- The construction lemma of recipe B. -/
theorem exists_goodB_family (d : I → ℕ → ℕ) (hd : ∀ α n, n ≤ d α n) :
    ∃ f, ∀ ξ, GoodB d ξ f :=
  local_recursion (GoodB d) (goodB_locality d) (goodB_extension d hd)

/-- The capture property at the stage assigned to a pair (the "in particular"
of Lemma 3.1). -/
theorem goodB_capture {d : I → ℕ → ℕ} (hd : ∀ α n, n ≤ d α n)
    {f : I → StageValue} (hf : ∀ ξ, GoodB d ξ f) (α β : I) {x : Set ℕ}
    (hx : K (d α) x) (hsub : x ⊆ traceClass d (members f) α β) :
    (x ∩ (f (gamma (α, β))).1).Infinite := by
  have h6 := (hf (gamma (α, β))).2.2.2.2.2
  simp only [stageClass, task_gamma] at h6
  have hall : {j | ¬ (traceClass d (members f) α β ∩ interval (d α) j).Nonempty}.Finite := by
    apply Set.finite_empty.subset
    intro j hj
    apply hj
    obtain ⟨i, hix, hij⟩ := K_meets_interval hx j
    exact ⟨i, hsub hix, hij⟩
  have hT := h6 hall
  apply Set.infinite_of_forall_exists_gt
  intro M
  obtain ⟨j, hj, hMj⟩ := hT.exists_gt M
  obtain ⟨i, hix, hij⟩ := K_meets_interval hx j
  exact ⟨i, ⟨hix, hj ⟨hsub hix, hij⟩⟩, lt_of_lt_of_le hMj ((le_h (hd α) j).trans hij.1)⟩

/-- The family of recipe B is MAD whenever the sequence dominates pointwise. -/
theorem goodB_MAD {d : I → ℕ → ℕ} (hd : ∀ α n, n ≤ d α n)
    (hdom : PointwiseDominating d) {f : I → StageValue} (hf : ∀ ξ, GoodB d ξ f) :
    MADFamily (members f) := by
  have hpair : Pairwise (fun i j => (members f i ∩ members f j).Finite) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · simpa only [members, Set.inter_comm] using (hf j).2.1 i h
    · exact (hf i).2.1 j h
  refine ⟨fun i => (hf i).1, hpair, ?_, ?_⟩
  · intro i j hij
    by_contra hne
    have hfin := hpair hne
    change (members f i ∩ members f j).Finite at hfin
    rw [hij, Set.inter_self] at hfin
    exact (hf j).1 hfin
  · intro x hx
    by_contra hn
    have hfinite : ∀ i, (x ∩ members f i).Finite := by
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩
    obtain ⟨α, hα⟩ := pointwise_covers_infinite hdom hx
    have htrace : ∀ k, (x ∩ earlier (members f) α k).Finite := by
      intro k
      cases he : enumEarlier α k with
      | none => simp [earlier, he]
      | some η => simpa [earlier, he] using hfinite η
    obtain ⟨β, hβ⟩ := pointwise_bounds_trace hdom htrace
    exact goodB_capture hd hf α β hα hβ (hfinite _)

theorem indexed_domination_implies_mad_recetaB
    {D : I → ℕ → ℕ} (hD : EventuallyDominating D) :
    ∃ A : I → Set ℕ, MADFamily A ∧ Cardinal.mk (Set.range A) = Cardinal.aleph 1 := by
  obtain ⟨f, hf⟩ := exists_goodB_family (normalizedI D) (normalizedI_ge_id D)
  have hmad := goodB_MAD (normalizedI_ge_id D) (normalizedI_pointwise hD) hf
  exact ⟨members f, hmad, MADFamily_cardinal hmad⟩

theorem dominating_aleph_one_implies_mad_aleph_one_recetaB
    {F : Set (ℕ → ℕ)} (hF : DominatingSet F)
    (hcard : Cardinal.mk F = Cardinal.aleph 1) :
    ∃ A : Set (Set ℕ), IsMAD A ∧ Cardinal.mk A = Cardinal.aleph 1 := by
  obtain ⟨D, hD⟩ := dominatingSet_indexed hF hcard
  obtain ⟨A, hA, hsize⟩ := indexed_domination_implies_mad_recetaB hD
  exact ⟨Set.range A, MADFamily_isMAD hA, hsize⟩

/-- The title theorem, proved through recipe B. -/
theorem d_eq_aleph_one_implies_a_eq_aleph_one_recetaB
    (hd : IsDominatingNumber (Cardinal.aleph 1)) :
    IsAlmostDisjointnessNumber (Cardinal.aleph 1) := by
  obtain ⟨F, hF, hcard⟩ := hd.1
  obtain ⟨D, hD⟩ := dominatingSet_indexed hF hcard
  obtain ⟨A, hA, _⟩ := indexed_domination_implies_mad_recetaB hD
  exact aleph_one_isAlmostDisjointnessNumber hA

end Roitman.RecetaB
