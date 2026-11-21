import Roitman.CHExtension
import Roitman.Maximality

/-! The combinatorial CH refinement. Forcing consequences are outside the
scope of this formalization. -/
noncomputable section
namespace Roitman
open Bookkeeping

theorem exists_good_CH_family (d : I → ℕ → ℕ) (hd : ∀ α n, n ≤ d α n)
    (X : I → Set (Finset ℕ)) : ∃ A, ∀ ξ, GoodAtCH d X ξ A :=
  ch_construction_of_extension d X (goodAtCH_extension d hd X)

/-- Under CH there is a MAD family of size aleph one which is almost strongly
separable, with positivity expressed against its generated ideal. -/
theorem ch_exists_almostStronglySeparable_MAD
    (hCH : Cardinal.continuum.{0} = Cardinal.aleph 1) :
    ∃ A : I → Set ℕ, MADFamily A ∧
      Cardinal.mk (Set.range A) = Cardinal.aleph 1 ∧ AlmostStronglySeparable A := by
  let e := chFunctionEnumeration hCH
  let d : I → ℕ → ℕ := fun α n => max n (e α n)
  have hd : ∀ α n, n ≤ d α n := fun _ _ => le_max_left _ _
  have hdom : PointwiseDominating d := by
    intro f
    refine ⟨e.symm f, ?_⟩
    intro n
    simp only [d, Equiv.apply_symm_apply]
    exact le_max_right _ _
  let X := chEnumeration hCH
  obtain ⟨A, hA⟩ := exists_good_CH_family d hd X
  have hmad : MADFamily A := good_MAD (fun ξ => (hA ξ).1) hdom
  exact ⟨A, hmad, MADFamily_cardinal hmad,
    goodCH_almostStronglySeparable X.surjective hA⟩

/-- The weaker finite-set selection property allows the capturing set to be
any member of the generated ideal. -/
def ShelahSteprans (A : I → Set ℕ) : Prop :=
  ∀ X, IdealPositive A X → ∃ B, InGeneratedIdeal A B ∧ Captured B X

theorem almostStronglySeparable_shelahSteprans {A : I → Set ℕ}
    (hA : AlmostStronglySeparable A) : ShelahSteprans A := by
  classical
  intro X hX
  obtain ⟨ξ, hξ⟩ := hA X ((positive_iff_idealPositive A X).mpr hX)
  refine ⟨A ξ, ?_, hξ⟩
  exact ⟨{ξ}, 0, fun i hi => Or.inr ⟨ξ, Finset.mem_singleton_self ξ, hi⟩⟩

end Roitman
