import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! Elementary combinatorics from Section 2 of the earlier draft of arXiv:2610.00639 (first construction). -/
namespace Roitman

noncomputable def count (x : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range (N + 1)).filter (fun i => i ∈ x)).card

def K (d : ℕ → ℕ) (x : Set ℕ) : Prop := ∀ n, n + 1 ≤ count x (d n)

def h (d : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => d (h d j) + 1

def interval (d : ℕ → ℕ) (j : ℕ) : Set ℕ := Set.Ico (h d j) (h d (j + 1))

def traceSet (c : ℕ → Set ℕ) (g : ℕ → ℕ) : Set ℕ :=
  {i | ∀ k, i ∈ c k → i < g k}

theorem count_mono {x y : Set ℕ} (hxy : x ⊆ y) (N : ℕ) : count x N ≤ count y N := by
  classical
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, hxy hi.2⟩

theorem K_mono {d : ℕ → ℕ} {x y : Set ℕ} (hx : K d x) (hxy : x ⊆ y) : K d y :=
  fun n => (hx n).trans (count_mono hxy (d n))

theorem count_le_card {x : Set ℕ} (hx : x.Finite) (N : ℕ) :
    count x N ≤ hx.toFinset.card := by
  classical
  apply Finset.card_le_card
  intro i hi
  exact hx.mem_toFinset.mpr (Finset.mem_filter.mp hi).2

theorem K_infinite {d : ℕ → ℕ} {x : Set ℕ} (hx : K d x) : x.Infinite := by
  intro hfin
  have h₁ := hx hfin.toFinset.card
  have h₂ := count_le_card hfin (d hfin.toFinset.card)
  omega

theorem h_strictMono {d : ℕ → ℕ} (hd : ∀ n, n ≤ d n) : StrictMono (h d) := by
  apply strictMono_nat_of_lt_succ
  intro j
  simp only [h]
  exact Nat.lt_succ_of_le (hd _)

theorem le_h {d : ℕ → ℕ} (hd : ∀ n, n ≤ d n) (j : ℕ) : j ≤ h d j :=
  (h_strictMono hd).id_le j

theorem interval_nonempty {d : ℕ → ℕ} (hd : ∀ n, n ≤ d n) (j : ℕ) :
    (interval d j).Nonempty :=
  ⟨h d j, le_rfl, (h_strictMono hd) (Nat.lt_succ_self j)⟩

theorem interval_finite (d : ℕ → ℕ) (j : ℕ) : (interval d j).Finite :=
  Set.finite_Ico _ _

theorem K_meets_interval {d : ℕ → ℕ} {x : Set ℕ} (hx : K d x) (j : ℕ) :
    (x ∩ interval d j).Nonempty := by
  classical
  by_contra hn
  have hsub : (Finset.range (d (h d j) + 1)).filter (fun i => i ∈ x) ⊆
      Finset.range (h d j) := by
    intro i hi
    obtain ⟨hi₁, hi₂⟩ := Finset.mem_filter.mp hi
    have hi₃ := Finset.mem_range.mp hi₁
    apply Finset.mem_range.mpr
    by_contra hi₄
    apply hn
    exact ⟨i, hi₂, by change h d j ≤ i ∧ i < d (h d j) + 1; omega⟩
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_range] at hc
  have hxj := hx (h d j)
  change h d j + 1 ≤ ((Finset.range (d (h d j) + 1)).filter (fun i => i ∈ x)).card at hxj
  omega

theorem not_K_of_missed_interval {d : ℕ → ℕ} {z : Set ℕ} {j : ℕ}
    (hz : Disjoint z (interval d j)) : ¬ K d z := by
  intro hk
  obtain ⟨i, hiz, hii⟩ := K_meets_interval hk j
  exact Set.disjoint_left.mp hz hiz hii

theorem infinite_diff_of_infinite_missed {d : ℕ → ℕ} (hd : ∀ n, n ≤ d n)
    {x z : Set ℕ} (hx : K d x)
    (hz : {j | Disjoint z (interval d j)}.Infinite) : (x \ z).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨j, hj, hNj⟩ := hz.exists_gt N
  obtain ⟨i, hix, hij⟩ := K_meets_interval hx j
  refine ⟨i, ⟨hix, ?_⟩, ?_⟩
  · intro hiz
    exact Set.disjoint_left.mp hj hiz hij
  · have := le_h hd j
    have := hij.1
    omega

theorem exists_count_le_of_not_K {d : ℕ → ℕ} {x : Set ℕ} (hx : ¬ K d x) :
    ∃ m, count x (d m) ≤ m := by
  simp only [K, not_forall, not_le] at hx
  obtain ⟨m, hm⟩ := hx
  exact ⟨m, by omega⟩

def hittingSet (G E : Set ℕ) (N : ℕ) : Set ℕ := (G \ E) ∩ Set.Iic N

theorem hittingSet_finite (G E : Set ℕ) (N : ℕ) : (hittingSet G E N).Finite :=
  (Set.finite_Iic N).subset (fun _ hi => hi.2)

theorem hittingSet_meets {G E x : Set ℕ} {N m : ℕ}
    (hGE : count (G ∩ E) N ≤ m) (hxG : x ⊆ G) (hx : m + 1 ≤ count x N) :
    (x ∩ hittingSet G E N).Nonempty := by
  classical
  by_contra hn
  have hc : count x N ≤ count (G ∩ E) N := by
    apply Finset.card_le_card
    intro i hi
    obtain ⟨hiN, hix⟩ := Finset.mem_filter.mp hi
    simp only [Finset.mem_filter, Set.mem_inter_iff]
    refine ⟨hiN, hxG hix, ?_⟩
    by_contra hiE
    apply hn
    refine ⟨i, hix, ⟨hxG hix, hiE⟩, ?_⟩
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hiN)
  omega

theorem finite_hitting {d : ℕ → ℕ} {G E : Set ℕ} (hG : K d G)
    (hGE : ¬ K d (G ∩ E)) :
    ∃ m, count (G ∩ E) (d m) ≤ m ∧
      (hittingSet G E (d m)).Finite ∧ (hittingSet G E (d m)).Nonempty ∧
      ∀ x, K d x → x ⊆ G → (x ∩ hittingSet G E (d m)).Nonempty := by
  obtain ⟨m, hm⟩ := exists_count_le_of_not_K hGE
  refine ⟨m, hm, hittingSet_finite _ _ _, ?_, ?_⟩
  · exact (hittingSet_meets hm (Set.Subset.refl G) (hG m)).mono Set.inter_subset_right
  · intro x hx hxG
    exact hittingSet_meets hm hxG (hx m)

theorem subset_traceSet_iff {x : Set ℕ} {c : ℕ → Set ℕ} {g : ℕ → ℕ} :
    x ⊆ traceSet c g ↔ ∀ k, x ∩ c k ⊆ Set.Iio (g k) := by
  constructor
  · intro hx k i hi
    exact hx hi.1 k hi.2
  · intro hx i hi k hic
    exact hx k ⟨hi, hic⟩

theorem traceSet_inter_finite (c : ℕ → Set ℕ) (g : ℕ → ℕ) (k : ℕ) :
    (traceSet c g ∩ c k).Finite :=
  (Set.finite_Iio (g k)).subset (fun _ hi => hi.1 k hi.2)

@[simp] theorem h_zero (d : ℕ → ℕ) : h d 0 = 0 := rfl
@[simp] theorem h_succ (d : ℕ → ℕ) (j : ℕ) : h d (j + 1) = d (h d j) + 1 := rfl

@[simp] theorem mem_interval {d : ℕ → ℕ} {j i : ℕ} :
    i ∈ interval d j ↔ h d j ≤ i ∧ i < h d (j + 1) := Iff.rfl

theorem intervals_disjoint {d : ℕ → ℕ} (hd : ∀ n, n ≤ d n) {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (interval d j) (interval d k) := by
  apply Set.disjoint_left.mpr
  intro i hij hik
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · have hh := (h_strictMono hd).monotone (Nat.succ_le_of_lt hjk)
    exact (not_lt_of_ge (hh.trans hik.1)) hij.2
  · have hh := (h_strictMono hd).monotone (Nat.succ_le_of_lt hkj)
    exact (not_lt_of_ge (hh.trans hij.1)) hik.2

theorem exists_trace_bound {x : Set ℕ} {c : ℕ → Set ℕ}
    (hx : ∀ k, (x ∩ c k).Finite) : ∃ g : ℕ → ℕ, x ⊆ traceSet c g := by
  have hb : ∀ k, ∃ N : ℕ, ∀ i ∈ x ∩ c k, i < N := by
    intro k
    obtain ⟨N, hN⟩ := (hx k).bddAbove
    exact ⟨N + 1, fun i hi => Nat.lt_succ_of_le (hN hi)⟩
  choose g hg using hb
  exact ⟨g, subset_traceSet_iff.mpr hg⟩

theorem traceSet_mono {c : ℕ → Set ℕ} {f g : ℕ → ℕ} (hfg : ∀ k, f k ≤ g k) :
    traceSet c f ⊆ traceSet c g := by
  intro i hi k hic
  exact (hi k hic).trans_le (hfg k)

end Roitman





