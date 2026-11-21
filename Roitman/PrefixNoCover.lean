import Roitman.CaptureStage
import Roitman.ConstructionDefs
import Roitman.NoCover
import Mathlib.Data.Finset.Option

noncomputable section
namespace Roitman
open Bookkeeping

/-- A finite union of members, used in the no-cover argument. -/
def memberUnion (A : I → Set ℕ) (u : Finset I) : Set ℕ :=
  ⋃ η ∈ u, A η

@[simp] theorem mem_memberUnion {A : I → Set ℕ} {u : Finset I} {i : ℕ} :
    i ∈ memberUnion A u ↔ ∃ η ∈ u, i ∈ A η := by
  simp [memberUnion]

/-- The finitely many actual indices appearing in the first `n+1` slots. -/
def prefixIndices (ξ : I) (n : ℕ) : Finset I :=
  (Finset.range (n + 1)).biUnion (fun k => (enumEarlier ξ k).toFinset)

theorem mem_prefixIndices {ξ η : I} {n : ℕ} :
    η ∈ prefixIndices ξ n ↔ ∃ k ≤ n, enumEarlier ξ k = some η := by
  simp [prefixIndices, Option.mem_def]

theorem prefixIndices_lt {ξ η : I} {n : ℕ} (h : η ∈ prefixIndices ξ n) : η < ξ := by
  obtain ⟨k, _, hk⟩ := mem_prefixIndices.mp h
  exact enumEarlier_lt hk

theorem exclusions_subset_prefix (A : I → Set ℕ) (ξ : I) (n b : ℕ) :
    exclusions (earlier A ξ) n b ⊆ Set.Iio b ∪ memberUnion A (prefixIndices ξ n) := by
  intro i hi
  rcases hi with hi | ⟨k, hk, hi⟩
  · exact Or.inl hi
  · right
    cases he : enumEarlier ξ k with
    | none => simp [earlier, he] at hi
    | some η =>
      apply mem_memberUnion.mpr
      exact ⟨η, mem_prefixIndices.mpr ⟨k, hk, he⟩, by simpa [earlier, he] using hi⟩

theorem gapIndices_union {d : I → ℕ → ℕ} {A : I → Set ℕ} {α : I}
    {u : Finset I} {j : ℕ} :
    j ∈ gapIndices d A α u ↔ Disjoint (memberUnion A u) (interval (d α) j) := by
  constructor
  · intro hj
    apply Set.disjoint_left.mpr
    intro i hi hii
    obtain ⟨η, hη, hiη⟩ := mem_memberUnion.mp hi
    exact Set.disjoint_left.mp (hj η hη) hiη hii
  · intro hj η hη
    apply Set.disjoint_left.mpr
    intro i hi hii
    exact Set.disjoint_left.mp hj (mem_memberUnion.mpr ⟨η, hη, hi⟩) hii

theorem traceClass_inter_earlier_finite (d : I → ℕ → ℕ) (A : I → Set ℕ)
    {α η : I} (β : I) (hη : η < α) : (traceClass d A α β ∩ A η).Finite := by
  obtain ⟨k, hk⟩ := enumEarlier_complete hη
  have hf := traceSet_inter_finite (earlier A α) (d β) k
  simpa [traceClass, earlier, hk] using hf

theorem traceClass_inter_memberUnion_finite (d : I → ℕ → ℕ) (A : I → Set ℕ)
    (α β : I) (u : Finset I) (hu : ∀ η ∈ u, η < α) :
    (traceClass d A α β ∩ memberUnion A u).Finite := by
  have hf : (⋃ η ∈ (u : Set I), traceClass d A α β ∩ A η).Finite :=
    u.finite_toSet.biUnion (fun η hη => traceClass_inter_earlier_finite d A β (hu η hη))
  apply hf.subset
  intro i hi
  obtain ⟨η, hη, hiη⟩ := mem_memberUnion.mp hi.2
  exact Set.mem_iUnion.mpr ⟨η, Set.mem_iUnion.mpr ⟨hη, hi.1, hiη⟩⟩

/-- The no-cover assertion used at any stage, derived from the gap invariant. -/
theorem prefix_noCover
    (d : I → ℕ → ℕ) (hd : ∀ α n, n ≤ d α n)
    (A : I → Set ℕ) (ξ α β : I) (hαξ : α ≤ ξ)
    (Hgap : ∀ γ ≤ ξ, ∀ u : Finset I,
      (∀ η ∈ u, γ ≤ η ∧ η < ξ) → (gapIndices d A γ u).Infinite) :
    ∀ n b, ¬ K (d α) (traceClass d A α β ∩ exclusions (earlier A ξ) n b) := by
  classical
  intro n b
  let u := prefixIndices ξ n
  let ue := u.filter (fun η => η < α)
  let ul := u.filter (fun η => α ≤ η)
  have hul : ∀ η ∈ ul, α ≤ η ∧ η < ξ := by
    intro η hη
    obtain ⟨hηu, hαη⟩ := Finset.mem_filter.mp hη
    exact ⟨hαη, prefixIndices_lt hηu⟩
  have hgap : {j | Disjoint (memberUnion A ul) (interval (d α) j)}.Infinite := by
    apply (Hgap α hαξ ul hul).mono
    intro j hj
    exact gapIndices_union.mp hj
  have hearly :
      (traceClass d A α β ∩ (Set.Iio b ∪ memberUnion A ue)).Finite := by
    have hfinite := traceClass_inter_memberUnion_finite d A α β ue
      (fun η hη => (Finset.mem_filter.mp hη).2)
    apply ((Set.finite_Iio b).union hfinite).subset
    intro i hi
    rcases hi.2 with hiB | hiE
    · exact Or.inl hiB
    · exact Or.inr ⟨hi.1, hiE⟩
  apply noCover (hd α) (early := Set.Iio b ∪ memberUnion A ue)
    (late := memberUnion A ul) ?_ hearly hgap
  intro i hi
  rcases exclusions_subset_prefix A ξ n b hi with hi | hi
  · exact Or.inl (Or.inl hi)
  · obtain ⟨η, hη, hiη⟩ := mem_memberUnion.mp hi
    by_cases hηα : η < α
    · exact Or.inl (Or.inr (mem_memberUnion.mpr
        ⟨η, Finset.mem_filter.mpr ⟨hη, hηα⟩, hiη⟩))
    · exact Or.inr (mem_memberUnion.mpr
        ⟨η, Finset.mem_filter.mpr ⟨hη, le_of_not_gt hηα⟩, hiη⟩)

/-- The alpha-zero gap invariant supplies a point outside every finite exclusion. -/
theorem prefix_escape
    (d : I → ℕ → ℕ) (hd : ∀ α n, n ≤ d α n)
    (A : I → Set ℕ) (ξ : I)
    (Hgap : ∀ γ ≤ ξ, ∀ u : Finset I,
      (∀ η ∈ u, γ ≤ η ∧ η < ξ) → (gapIndices d A γ u).Infinite) :
    ∀ n b, ∃ i, i ∉ exclusions (earlier A ξ) n b := by
  intro n b
  have hg := Hgap ⊥ bot_le (prefixIndices ξ n)
    (fun η hη => ⟨bot_le, prefixIndices_lt hη⟩)
  have hgap : {j | Disjoint (memberUnion A (prefixIndices ξ n))
      (interval (d ⊥) j)}.Infinite := by
    apply hg.mono
    intro j hj
    exact gapIndices_union.mp hj
  have hg' := gaps_finite_union (hd ⊥) (Set.finite_Iio b) hgap
  obtain ⟨j, hj⟩ := hg'.nonempty
  obtain ⟨i, hi⟩ := interval_nonempty (hd ⊥) j
  refine ⟨i, ?_⟩
  intro hiE
  exact Set.disjoint_left.mp hj (exclusions_subset_prefix A ξ n b hiE) hi

end Roitman
