import Roitman.Maximality

noncomputable section
namespace Roitman

/-- A countably indexed almost disjoint sequence is not maximal. -/
theorem countable_AD_has_avoider (A : ℕ → Set ℕ)
    (hinf : ∀ n, (A n).Infinite)
    (had : Pairwise (fun n m => (A n ∩ A m).Finite)) :
    ∃ x : Set ℕ, x.Infinite ∧ ∀ n, (x ∩ A n).Finite := by
  classical
  have hav : ∀ n, ∃ i, n < i ∧ i ∈ A n ∧ ∀ k < n, i ∉ A k := by
    intro n
    let E : Set ℕ := ⋃ k ∈ Set.Iio n, A n ∩ A k
    have hE : E.Finite := by
      apply (Set.finite_Iio n).biUnion
      intro k hk
      exact had (show n ≠ k from ne_of_gt hk)
    obtain ⟨i, hi, hni⟩ := ((hinf n).sdiff hE).exists_gt n
    refine ⟨i, hni, hi.1, ?_⟩
    intro k hk hik
    exact hi.2 (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, hi.1, hik⟩⟩)
  choose f hf using hav
  refine ⟨Set.range f, ?_, ?_⟩
  · apply Set.infinite_of_forall_exists_gt
    intro n
    exact ⟨f n, ⟨n, rfl⟩, (hf n).1⟩
  · intro k
    apply ((Set.finite_Iic k).image f).subset
    rintro i ⟨⟨n, rfl⟩, hA⟩
    refine ⟨n, ?_, rfl⟩
    by_contra hn
    exact (hf n).2.2 k (by simpa using hn) hA

theorem IsMAD_not_countable {F : Set (Set ℕ)} (hF : IsMAD F) : ¬ F.Countable := by
  intro hc
  let : Countable F := hc.to_subtype
  let : Infinite F := hF.1.to_subtype
  let e : ℕ ≃ F := Classical.choice (Cardinal.eq.mp (by simp))
  let A : ℕ → Set ℕ := fun n => (e n).val
  have hinf : ∀ n, (A n).Infinite := fun n => hF.2.1 _ (e n).property
  have had : Pairwise (fun n m => (A n ∩ A m).Finite) := by
    intro n m hnm
    apply hF.2.2.1 (e n).property (e m).property
    intro h
    exact hnm (e.injective (Subtype.ext h))
  obtain ⟨x, hx, hxA⟩ := countable_AD_has_avoider A hinf had
  obtain ⟨a, haF, hxa⟩ := hF.2.2.2 x hx
  have hfin := hxA (e.symm ⟨a, haF⟩)
  exact hxa (by simpa [A] using hfin)

theorem IsMAD_cardinal_lower_bound {F : Set (Set ℕ)} (hF : IsMAD F) :
    Cardinal.aleph 1 ≤ Cardinal.mk F := by
  by_contra h
  have hc : Cardinal.mk F ≤ Cardinal.aleph0 :=
    Cardinal.lt_aleph_one_iff.mp (lt_of_not_ge h)
  exact IsMAD_not_countable hF (Cardinal.mk_le_aleph0_iff.mp hc)

/-- A direct least-cardinality formulation of the almost disjointness number. -/
def IsAlmostDisjointnessNumber (κ : Cardinal) : Prop :=
  (∃ F : Set (Set ℕ), IsMAD F ∧ Cardinal.mk F = κ) ∧
  ∀ F : Set (Set ℕ), IsMAD F → κ ≤ Cardinal.mk F

theorem aleph_one_isAlmostDisjointnessNumber {A : Roitman.Bookkeeping.I → Set ℕ}
    (hA : MADFamily A) : IsAlmostDisjointnessNumber (Cardinal.aleph 1) :=
  ⟨⟨Set.range A, MADFamily_isMAD hA, MADFamily_cardinal hA⟩,
    fun _ hF => IsMAD_cardinal_lower_bound hF⟩

/-- A direct least-cardinality formulation of the dominating number. -/
def IsDominatingNumber (κ : Cardinal) : Prop :=
  (∃ F : Set (ℕ → ℕ), DominatingSet F ∧ Cardinal.mk F = κ) ∧
  ∀ F : Set (ℕ → ℕ), DominatingSet F → κ ≤ Cardinal.mk F

theorem IsAlmostDisjointnessNumber_unique {κ μ : Cardinal}
    (hκ : IsAlmostDisjointnessNumber κ) (hμ : IsAlmostDisjointnessNumber μ) : κ = μ := by
  obtain ⟨F, hF, hFcard⟩ := hκ.1
  obtain ⟨G, hG, hGcard⟩ := hμ.1
  exact le_antisymm (hGcard ▸ hκ.2 G hG) (hFcard ▸ hμ.2 F hF)

theorem IsDominatingNumber_unique {κ μ : Cardinal}
    (hκ : IsDominatingNumber κ) (hμ : IsDominatingNumber μ) : κ = μ := by
  obtain ⟨F, hF, hFcard⟩ := hκ.1
  obtain ⟨G, hG, hGcard⟩ := hμ.1
  exact le_antisymm (hGcard ▸ hκ.2 G hG) (hFcard ▸ hμ.2 F hF)

theorem d_eq_aleph_one_implies_a_eq_aleph_one_of_construction
    (construction : ∀ (d : Bookkeeping.I → ℕ → ℕ), (∀ i n, n ≤ d i n) →
      ∃ A, ∀ ξ, GoodAt d Bookkeeping.task ξ A)
    (hd : IsDominatingNumber (Cardinal.aleph 1)) :
    IsAlmostDisjointnessNumber (Cardinal.aleph 1) := by
  obtain ⟨F, hF, hcard⟩ := hd.1
  obtain ⟨A, hA, _⟩ := dominatingSet_implies_MAD_of_construction construction hF hcard
  exact aleph_one_isAlmostDisjointnessNumber hA

end Roitman




