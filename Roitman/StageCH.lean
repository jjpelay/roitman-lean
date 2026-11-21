import Roitman.Stage
import Mathlib.Data.Set.Finite.Lattice

/-! Finite-block stage with witnesses for the CH refinement. -/
namespace Roitman

theorem finiteBlocksStageCH
    (previous : ℕ → Set ℕ) (targets : Set (Set ℕ)) (X : Set (Finset ℕ))
    (intervals : ℕ → ℕ → Finset ℕ) (allowed : ℕ → Set ℕ)
    (schedule : ℕ → ℕ) (fair : FairSchedule schedule)
    (blocks : ∀ n b : ℕ, ∃ s : Finset ℕ,
      s.Nonempty ∧
      (∀ i ∈ s, b ≤ i) ∧
      (∀ k ≤ n, ∀ i ∈ s, i ∉ previous k) ∧
      (∀ x ∈ targets, ∃ i ∈ s, i ∈ x) ∧
      (∃ t ∈ X, t.Nonempty ∧ t ⊆ s))
    (gaps : ∀ r M : ℕ, ∃ j : ℕ,
      M ≤ j ∧ j ∈ allowed r ∧ ∀ i ∈ intervals r j, M ≤ i) :
    ∃ a : Set ℕ,
      a.Infinite ∧
      (∀ k, (a ∩ previous k).Finite) ∧
      (∀ x ∈ targets, (x ∩ a).Infinite) ∧
      (∀ r, {j | j ∈ allowed r ∧ ∀ i ∈ intervals r j, i ∉ a}.Infinite) ∧
      {t : Finset ℕ | t ∈ X ∧ (↑t : Set ℕ) ⊆ a}.Infinite := by
  classical
  let Step (n b : ℕ) (v : ℕ × Finset ℕ × ℕ) : Prop :=
    b < v.1 ∧ v.2.1.Nonempty ∧
    (∀ i ∈ v.2.1, b ≤ i ∧ i < v.1) ∧
    (∀ k ≤ n, ∀ i ∈ v.2.1, i ∉ previous k) ∧
    (∀ x ∈ targets, ∃ i ∈ v.2.1, i ∈ x) ∧
    n ≤ v.2.2 ∧ v.2.2 ∈ allowed (schedule n) ∧
    (∀ i ∈ intervals (schedule n) v.2.2,
      b ≤ i ∧ i < v.1 ∧ ∀ z ∈ v.2.1, z < i) ∧
    (∃ t ∈ X, t.Nonempty ∧ t ⊆ v.2.1)
  have localChoice (n b : ℕ) : ∃ v, Step n b v := by
    obtain ⟨s, hs, hlow, hav, hhit, htrack⟩ := blocks n b
    let M := max (n + 1) (s.sup id + 1)
    obtain ⟨j, hj, hallowed, hgap⟩ := gaps (schedule n) M
    let B := max (max b (s.sup id)) ((intervals (schedule n) j).sup id) + 1
    refine ⟨(B, s, j), ?_⟩
    dsimp only [Step]
    refine ⟨?_, hs, ?_, hav, hhit, ?_, hallowed, ?_, htrack⟩
    · dsimp [B]
      omega
    · intro i hi
      have his : i ≤ s.sup id := Finset.le_sup (f := id) hi
      dsimp [B]
      exact ⟨hlow i hi, by omega⟩
    · dsimp [M] at hj
      omega
    · intro i hi
      have hilow := hgap i hi
      have hiup : i ≤ (intervals (schedule n) j).sup id :=
        Finset.le_sup (f := id) hi
      obtain ⟨z, hz⟩ := hs
      have hzlow := hlow z hz
      have hzup : z ≤ s.sup id := Finset.le_sup (f := id) hz
      refine ⟨?_, ?_, ?_⟩
      · dsimp [M] at hilow
        omega
      · dsimp [B]
        omega
      · intro z hz
        have hzup : z ≤ s.sup id := Finset.le_sup (f := id) hz
        dsimp [M] at hilow
        omega
  let next (n b : ℕ) := Classical.choose (localChoice n b)
  have next_spec (n b : ℕ) : Step n b (next n b) :=
    Classical.choose_spec (localChoice n b)
  let b : ℕ → ℕ := fun n => Nat.rec 0 (fun n v => (next n v).1) n
  let s (n : ℕ) := (next n (b n)).2.1
  let j (n : ℕ) := (next n (b n)).2.2
  have bsucc (n : ℕ) : b (n + 1) = (next n (b n)).1 := rfl
  have spec (n : ℕ) :
      b n < b (n + 1) ∧ (s n).Nonempty ∧
      (∀ i ∈ s n, b n ≤ i ∧ i < b (n + 1)) ∧
      (∀ k ≤ n, ∀ i ∈ s n, i ∉ previous k) ∧
      (∀ x ∈ targets, ∃ i ∈ s n, i ∈ x) ∧
      n ≤ j n ∧ j n ∈ allowed (schedule n) ∧
      (∀ i ∈ intervals (schedule n) (j n),
        b n ≤ i ∧ i < b (n + 1) ∧ ∀ z ∈ s n, z < i) ∧
      (∃ t ∈ X, t.Nonempty ∧ t ⊆ s n) := by
    exact next_spec n (b n)
  have bstrict : StrictMono b := strictMono_nat_of_lt_succ fun n => (spec n).1
  have bn (n : ℕ) : n ≤ b n := bstrict.id_le n
  let a : Set ℕ := {i | ∃ n, i ∈ s n}
  have gapAvoid (n : ℕ) : ∀ i ∈ intervals (schedule n) (j n), i ∉ a := by
    intro i hi ⟨m, hm⟩
    have hs := (spec m).2.2.1 i hm
    have hg := (spec n).2.2.2.2.2.2.2.1 i hi
    rcases lt_trichotomy m n with hmn | hmn | hmn
    · have hb : b (m + 1) ≤ b n := bstrict.monotone (Nat.succ_le_of_lt hmn)
      omega
    · subst m
      have := hg.2.2 i hm
      omega
    · have hb : b (n + 1) ≤ b m := bstrict.monotone (Nat.succ_le_of_lt hmn)
      omega
  refine ⟨a, ?_, ?_, ?_, ?_, ?_⟩
  · apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨i, hi⟩ := (spec (N + 1)).2.1
    refine ⟨i, ⟨N + 1, hi⟩, ?_⟩
    have := (spec (N + 1)).2.2.1 i hi
    have := bn (N + 1)
    omega
  · intro k
    apply (Set.finite_Iio (b k)).subset
    intro i hi
    obtain ⟨n, hn⟩ := hi.1
    by_cases hkn : k ≤ n
    · exact False.elim ((spec n).2.2.2.1 k hkn i hn hi.2)
    · have hb := bstrict.monotone (show n + 1 ≤ k by omega)
      have hs := (spec n).2.2.1 i hn
      exact lt_of_lt_of_le hs.2 hb
  · intro x hx
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨i, hi, hix⟩ := (spec (N + 1)).2.2.2.2.1 x hx
    refine ⟨i, ⟨hix, N + 1, hi⟩, ?_⟩
    have := (spec (N + 1)).2.2.1 i hi
    have := bn (N + 1)
    omega
  · intro r
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨n, hn, heq⟩ := fair r (N + 1)
    refine ⟨j n, ⟨?_, ?_⟩, ?_⟩
    · simpa [heq] using (spec n).2.2.2.2.2.2.1
    · simpa [heq] using gapAvoid n
    · have := (spec n).2.2.2.2.2.1
      omega

  · intro hf
    have hUnion : (⋃ t ∈ {t : Finset ℕ | t ∈ X ∧ (↑t : Set ℕ) ⊆ a},
        (↑t : Set ℕ)).Finite := hf.biUnion (fun t _ => t.finite_toSet)
    obtain ⟨N, hN⟩ := hUnion.bddAbove
    obtain ⟨t, htX, ⟨i, hit⟩, hts⟩ := (spec (N + 1)).2.2.2.2.2.2.2.2
    have hta : (↑t : Set ℕ) ⊆ a := fun z hz => ⟨N + 1, hts hz⟩
    have hiUnion : i ∈ ⋃ t ∈ {t : Finset ℕ | t ∈ X ∧ (↑t : Set ℕ) ⊆ a},
        (↑t : Set ℕ) :=
      Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨⟨htX, hta⟩, hit⟩⟩
    have hiN := hN hiUnion
    have hilow := ((spec (N + 1)).2.2.1 i (hts hit)).1
    have := bn (N + 1)
    omega

end Roitman
