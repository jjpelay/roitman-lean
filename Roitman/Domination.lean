import Roitman.Basic
namespace Roitman

theorem count_mono_bound (x : Set ℕ) {N M : ℕ} (hNM : N ≤ M) :
    count x N ≤ count x M := by
  classical
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hiN, hix⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hiN; omega), hix⟩

theorem infinite_exists_K {x : Set ℕ} (hx : x.Infinite) :
    ∃ d : ℕ → ℕ, (∀ n, n ≤ d n) ∧ K d x := by
  classical
  have hb : ∀ n, ∃ N, n + 1 ≤ count x N := by
    intro n
    obtain ⟨t, htx, htcard⟩ := hx.exists_subset_card_eq (n + 1)
    refine ⟨t.sup id, ?_⟩
    rw [← htcard]
    apply Finset.card_le_card
    intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, htx hi⟩
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  choose d hd using hb
  refine ⟨fun n => max n (d n), fun n => le_max_left _ _, ?_⟩
  intro n
  exact (hd n).trans (count_mono_bound x (le_max_right _ _))

/-- A family cofinal for eventual domination. -/
def EventuallyDominating {ι : Type*} (D : ι → ℕ → ℕ) : Prop :=
  ∀ f : ℕ → ℕ, ∃ i N, ∀ n, N ≤ n → f n ≤ D i n

/-- A family cofinal for pointwise domination. -/
def PointwiseDominating {ι : Type*} (D : ι → ℕ → ℕ) : Prop :=
  ∀ f : ℕ → ℕ, ∃ i, ∀ n, f n ≤ D i n

/-- Closing under finite changes, while enforcing the lower bound by the identity. -/
def normalized {ι : Type*} (D : ι → ℕ → ℕ) (p : ι × List ℕ) (n : ℕ) : ℕ :=
  max n (max (D p.1 n) (p.2[n]?.getD 0))

theorem normalized_ge_id {ι : Type*} (D : ι → ℕ → ℕ) (p : ι × List ℕ) (n : ℕ) :
    n ≤ normalized D p n := le_max_left _ _

theorem normalized_pointwise {ι : Type*} {D : ι → ℕ → ℕ} (hD : EventuallyDominating D) :
    PointwiseDominating (normalized D) := by
  intro f
  obtain ⟨i, N, hi⟩ := hD f
  refine ⟨(i, List.ofFn (fun n : Fin N => f n)), ?_⟩
  intro n
  by_cases hn : n < N
  · have hprefix : (List.ofFn (fun k : Fin N => f k))[n]?.getD 0 = f n := by
      simp [hn]
    unfold normalized
    rw [hprefix]
    exact (le_max_right _ _).trans (le_max_right _ _)
  · exact (hi n (by omega)).trans ((le_max_left _ _).trans (le_max_right _ _))

theorem pointwise_covers_infinite {ι : Type*} {D : ι → ℕ → ℕ}
    (hD : PointwiseDominating D) {x : Set ℕ} (hx : x.Infinite) : ∃ i, K (D i) x := by
  obtain ⟨f, _, hf⟩ := infinite_exists_K hx
  obtain ⟨i, hi⟩ := hD f
  exact ⟨i, fun n => (hf n).trans (count_mono_bound x (hi n))⟩

theorem pointwise_bounds_trace {ι : Type*} {D : ι → ℕ → ℕ}
    (hD : PointwiseDominating D) {x : Set ℕ} {c : ℕ → Set ℕ}
    (hx : ∀ k, (x ∩ c k).Finite) : ∃ i, x ⊆ traceSet c (D i) := by
  obtain ⟨f, hf⟩ := exists_trace_bound hx
  obtain ⟨i, hi⟩ := hD f
  exact ⟨i, hf.trans (traceSet_mono hi)⟩

end Roitman


