import Roitman.Construction
import Roitman.Maximality
import Roitman.CardinalBounds

namespace Roitman
open Bookkeeping

/-- The title theorem, with both cardinal invariants expressed as least
cardinalities (existence of a witness plus the universal lower bound). -/
theorem d_eq_aleph_one_implies_a_eq_aleph_one
    (hd : IsDominatingNumber (Cardinal.aleph 1)) :
    IsAlmostDisjointnessNumber (Cardinal.aleph 1) :=
  d_eq_aleph_one_implies_a_eq_aleph_one_of_construction exists_good_family hd

/-- Main combinatorial conclusion, with the hypothesis and conclusion stated
as actual families of functions and sets, with their actual cardinalities.
The construction is proved, not assumed. -/
theorem dominating_aleph_one_implies_mad_aleph_one
    {D : Set (ℕ → ℕ)} (hD : DominatingSet D)
    (hcard : Cardinal.mk D = Cardinal.aleph 1) :
    ∃ A : Set (Set ℕ), IsMAD A ∧ Cardinal.mk A = Cardinal.aleph 1 := by
  obtain ⟨A, hA, hsize⟩ :=
    dominatingSet_implies_MAD_of_construction exists_good_family hD hcard
  exact ⟨Set.range A, MADFamily_isMAD hA, hsize⟩

theorem indexed_domination_implies_mad
    {D : I → ℕ → ℕ} (hD : EventuallyDominating D) :
    ∃ A : I → Set ℕ, MADFamily A ∧ Cardinal.mk (Set.range A) = Cardinal.aleph 1 :=
  eventualDomination_implies_MAD_of_construction exists_good_family hD

end Roitman
