import Roitman.ConstructionDefs
import Roitman.Domination

noncomputable section
namespace Roitman
open Bookkeeping

/-- The indexed version of an infinite maximal almost disjoint family. -/
def MADFamily (A : I → Set ℕ) : Prop :=
  (∀ i, (A i).Infinite) ∧
  Pairwise (fun i j => (A i ∩ A j).Finite) ∧
  Function.Injective A ∧
  ∀ x : Set ℕ, x.Infinite → ∃ i, (x ∩ A i).Infinite

theorem good_pairwise {d : I → ℕ → ℕ} {A : I → Set ℕ}
    (hA : ∀ ξ, GoodAt d task ξ A) : Pairwise (fun i j => (A i ∩ A j).Finite) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · simpa only [Set.inter_comm] using (hA j).2.1 i h
  · exact (hA i).2.1 j h

theorem good_injective {d : I → ℕ → ℕ} {A : I → Set ℕ}
    (hA : ∀ ξ, GoodAt d task ξ A) : Function.Injective A := by
  intro i j hij
  by_contra hne
  have hfin := good_pairwise hA hne
  change (A i ∩ A j).Finite at hfin
  rw [hij, Set.inter_self] at hfin
  exact (hA j).1 hfin

theorem good_maximal {d : I → ℕ → ℕ} {A : I → Set ℕ}
    (hA : ∀ ξ, GoodAt d task ξ A) (hd : PointwiseDominating d)
    {x : Set ℕ} (hx : x.Infinite) : ∃ i, (x ∩ A i).Infinite := by
  classical
  by_contra hn
  have hfinite : ∀ i, (x ∩ A i).Finite := by
    intro i
    by_contra hi
    exact hn ⟨i, hi⟩
  obtain ⟨α, hα⟩ := pointwise_covers_infinite hd hx
  have htrace : ∀ k, (x ∩ earlier A α k).Finite := by
    intro k
    cases he : enumEarlier α k with
    | none => simp [earlier, he]
    | some η => simpa [earlier, he] using hfinite η
  obtain ⟨β, hβ⟩ := pointwise_bounds_trace hd htrace
  have hcapture := (hA (gamma (α, β))).2.2.2
  rw [task_gamma] at hcapture
  have hcap : (x ∩ A (gamma (α, β))).Infinite := hcapture x hα hβ
  exact hcap (hfinite _)

theorem good_MAD {d : I → ℕ → ℕ} {A : I → Set ℕ}
    (hA : ∀ ξ, GoodAt d task ξ A) (hd : PointwiseDominating d) : MADFamily A :=
  ⟨fun i => (hA i).1, good_pairwise hA, good_injective hA, fun _ hx => good_maximal hA hd hx⟩

theorem MADFamily_cardinal {A : I → Set ℕ} (hA : MADFamily A) :
    Cardinal.mk (Set.range A) = Cardinal.aleph 1 := by
  rw [Cardinal.mk_range_eq A hA.2.2.1, cardinal_I]

/-- Finite changes add only a countable factor to the index set. -/
def normalizationEquiv : (I × List ℕ) ≃ I := Bookkeeping.normalizedIndexEquiv

/-- A pointwise family indexed again by omega one. -/
def normalizedI (D : I → ℕ → ℕ) (i : I) : ℕ → ℕ :=
  normalized D (normalizationEquiv.symm i)

theorem normalizedI_ge_id (D : I → ℕ → ℕ) (i : I) (n : ℕ) :
    n ≤ normalizedI D i n := normalized_ge_id _ _ _

theorem normalizedI_pointwise {D : I → ℕ → ℕ} (hD : EventuallyDominating D) :
    PointwiseDominating (normalizedI D) := by
  intro f
  obtain ⟨p, hp⟩ := normalized_pointwise hD f
  refine ⟨normalizationEquiv p, ?_⟩
  simpa [normalizedI] using hp

/-- Combining the construction with the two uses of domination. The construction
is an explicit premise here so this module is independent of its recursion proof. -/
theorem eventualDomination_implies_MAD_of_construction
    (construction : ∀ (d : I → ℕ → ℕ), (∀ i n, n ≤ d i n) →
      ∃ A, ∀ ξ, GoodAt d task ξ A)
    {D : I → ℕ → ℕ} (hD : EventuallyDominating D) :
    ∃ A : I → Set ℕ, MADFamily A ∧ Cardinal.mk (Set.range A) = Cardinal.aleph 1 := by
  obtain ⟨A, hA⟩ := construction (normalizedI D) (normalizedI_ge_id D)
  have hmad := good_MAD hA (normalizedI_pointwise hD)
  exact ⟨A, hmad, MADFamily_cardinal hmad⟩

/-- Domination expressed directly for a set of functions. -/
def DominatingSet (F : Set (ℕ → ℕ)) : Prop :=
  ∀ f : ℕ → ℕ, ∃ g ∈ F, ∃ N, ∀ n, N ≤ n → f n ≤ g n

theorem dominatingSet_indexed {F : Set (ℕ → ℕ)}
    (hF : DominatingSet F) (hcard : Cardinal.mk F = Cardinal.aleph 1) :
    ∃ D : I → ℕ → ℕ, EventuallyDominating D := by
  let e : I ≃ F := Classical.choice (Cardinal.eq.mp (cardinal_I.trans hcard.symm))
  refine ⟨fun i => (e i).val, ?_⟩
  intro f
  obtain ⟨g, hgF, N, hg⟩ := hF f
  refine ⟨e.symm ⟨g, hgF⟩, N, ?_⟩
  simpa using hg

theorem dominatingSet_implies_MAD_of_construction
    (construction : ∀ (d : I → ℕ → ℕ), (∀ i n, n ≤ d i n) →
      ∃ A, ∀ ξ, GoodAt d task ξ A)
    {F : Set (ℕ → ℕ)} (hF : DominatingSet F)
    (hcard : Cardinal.mk F = Cardinal.aleph 1) :
    ∃ A : I → Set ℕ, MADFamily A ∧ Cardinal.mk (Set.range A) = Cardinal.aleph 1 := by
  obtain ⟨D, hD⟩ := dominatingSet_indexed hF hcard
  exact eventualDomination_implies_MAD_of_construction construction hD

/-- The usual set-theoretic definition of an infinite MAD family. -/
def IsMAD (F : Set (Set ℕ)) : Prop :=
  F.Infinite ∧ (∀ a ∈ F, a.Infinite) ∧
  F.Pairwise (fun a b => (a ∩ b).Finite) ∧
  ∀ x : Set ℕ, x.Infinite → ∃ a ∈ F, (x ∩ a).Infinite

theorem MADFamily_isMAD {A : I → Set ℕ} (hA : MADFamily A) : IsMAD (Set.range A) := by
  let : Infinite I := Cardinal.aleph0_le_mk_iff.mp (by
    rw [cardinal_I]
    exact Cardinal.aleph0_lt_aleph_one.le)
  refine ⟨Set.infinite_range_of_injective hA.2.2.1, ?_, ?_, ?_⟩
  · rintro a ⟨i, rfl⟩
    exact hA.1 i
  · rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩ hij
    exact hA.2.1 (fun h => hij (congrArg A h))
  · intro x hx
    obtain ⟨i, hi⟩ := hA.2.2.2 x hx
    exact ⟨A i, ⟨i, rfl⟩, hi⟩

end Roitman





