import Roitman.Main
import Mathlib.SetTheory.Cardinal.Continuum

noncomputable section
namespace Roitman

/-- The usual diagonal proof that no countable family is eventually dominating. -/
theorem DominatingSet_not_countable {F : Set (ℕ → ℕ)}
    (hF : DominatingSet F) : ¬ F.Countable := by
  classical
  intro hc
  let : Countable F := hc.to_subtype
  obtain ⟨g₀, hg₀, _⟩ := hF (fun _ => 0)
  let : Nonempty F := ⟨⟨g₀, hg₀⟩⟩
  let e : ℕ → F := Bookkeeping.enumerate F
  let f : ℕ → ℕ := fun n => (Finset.range (n + 1)).sup (fun k => (e k).val n) + 1
  obtain ⟨g, hg, N, hdom⟩ := hF f
  obtain ⟨k, hk⟩ := Bookkeeping.enumerate_surjective F (⟨g, hg⟩ : F)
  let n := max k N
  have hn : N ≤ n := le_max_right _ _
  have hkn : k < n + 1 := Nat.lt_succ_of_le (le_max_left _ _)
  have hsup := Finset.le_sup (s := Finset.range (n + 1))
    (f := fun k => (e k).val n) (Finset.mem_range.mpr hkn)
  have he : (e k).val = g := congrArg Subtype.val hk
  rw [he] at hsup
  have hbound := hdom n hn
  change (Finset.range (n + 1)).sup (fun k => (e k).val n) + 1 ≤ g n at hbound
  omega

theorem DominatingSet_cardinal_lower_bound {F : Set (ℕ → ℕ)}
    (hF : DominatingSet F) : Cardinal.aleph.{0} 1 ≤ Cardinal.mk F := by
  by_contra h
  have hc : Cardinal.mk F ≤ Cardinal.aleph0 :=
    Cardinal.lt_aleph_one_iff.mp (lt_of_not_ge h)
  exact DominatingSet_not_countable hF (Cardinal.mk_le_aleph0_iff.mp hc)

theorem dominatingNumber_lower_bound {d : Cardinal} (hd : IsDominatingNumber d) :
    Cardinal.aleph.{0} 1 ≤ d := by
  obtain ⟨F, hF, rfl⟩ := hd.1
  exact DominatingSet_cardinal_lower_bound hF

theorem almostDisjointnessNumber_lower_bound {a : Cardinal}
    (ha : IsAlmostDisjointnessNumber a) : Cardinal.aleph.{0} 1 ≤ a := by
  obtain ⟨F, hF, rfl⟩ := ha.1
  exact IsMAD_cardinal_lower_bound hF

theorem almostDisjointnessNumber_le_continuum {a : Cardinal}
    (ha : IsAlmostDisjointnessNumber a) : a ≤ Cardinal.continuum.{0} := by
  obtain ⟨F, _, rfl⟩ := ha.1
  simpa only [Cardinal.mk_set_nat] using Cardinal.mk_set_le F

theorem dominatingNumber_le_continuum {d : Cardinal}
    (hd : IsDominatingNumber d) : d ≤ Cardinal.continuum.{0} := by
  obtain ⟨F, _, rfl⟩ := hd.1
  simpa only [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.mk_nat,
    Cardinal.aleph0_power_aleph0] using Cardinal.mk_set_le F

/-- The first assertion of Corollary 1.2. -/
theorem a_le_d_of_d_eq_aleph_one_or_continuum {a d : Cardinal}
    (ha : IsAlmostDisjointnessNumber a) (hd : IsDominatingNumber d)
    (hc : d = Cardinal.aleph.{0} 1 ∨ d = Cardinal.continuum.{0}) : a ≤ d := by
  rcases hc with h | h
  · subst d
    exact (IsAlmostDisjointnessNumber_unique ha
      (d_eq_aleph_one_implies_a_eq_aleph_one hd)).le
  · rw [h]
    exact almostDisjointnessNumber_le_continuum ha

/-- With continuum at most aleph two, the dominating number is either
aleph one or the continuum. -/
theorem d_eq_aleph_one_or_continuum_of_small_continuum {d : Cardinal}
    (hd : IsDominatingNumber d) (hc : Cardinal.continuum.{0} ≤ Cardinal.aleph.{0} 2) :
    d = Cardinal.aleph.{0} 1 ∨ d = Cardinal.continuum.{0} := by
  by_cases h : d = Cardinal.aleph.{0} 1
  · exact Or.inl h
  · right
    have hlarge : Cardinal.aleph.{0} 1 < d :=
      lt_of_le_of_ne (dominatingNumber_lower_bound hd) (Ne.symm h)
    have htwo : Cardinal.aleph.{0} 2 ≤ d := by
      simpa only [Cardinal.succ_aleph, one_add_one_eq_two] using Order.succ_le_of_lt hlarge
    exact le_antisymm (dominatingNumber_le_continuum hd) (hc.trans htwo)

/-- In particular, continuum at most aleph two implies a ≤ d. -/
theorem a_le_d_of_continuum_le_aleph_two {a d : Cardinal}
    (ha : IsAlmostDisjointnessNumber a) (hd : IsDominatingNumber d)
    (hc : Cardinal.continuum.{0} ≤ Cardinal.aleph.{0} 2) : a ≤ d :=
  a_le_d_of_d_eq_aleph_one_or_continuum ha hd
    (d_eq_aleph_one_or_continuum_of_small_continuum hd hc)

/-- Any strict counterexample to a ≤ d must have d at least aleph two,
and a and the continuum at least aleph three. -/
theorem strict_d_lt_a_lower_bounds {a d : Cardinal}
    (ha : IsAlmostDisjointnessNumber a) (hd : IsDominatingNumber d) (hda : d < a) :
    Cardinal.aleph.{0} 2 ≤ d ∧ Cardinal.aleph.{0} 3 ≤ a ∧
      a ≤ Cardinal.continuum.{0} ∧ Cardinal.aleph.{0} 3 ≤ Cardinal.continuum.{0} := by
  have hne : d ≠ Cardinal.aleph.{0} 1 := by
    intro heq
    exact (not_le_of_gt hda) (a_le_d_of_d_eq_aleph_one_or_continuum ha hd (Or.inl heq))
  have hone : Cardinal.aleph.{0} 1 < d :=
    lt_of_le_of_ne (dominatingNumber_lower_bound hd) (Ne.symm hne)
  have htwo : Cardinal.aleph.{0} 2 ≤ d := by
    simpa only [Cardinal.succ_aleph, one_add_one_eq_two] using Order.succ_le_of_lt hone
  have hthree : Cardinal.aleph.{0} 3 ≤ a := by
    convert Order.succ_le_of_lt (htwo.trans_lt hda) using 1 <;> norm_num [Cardinal.succ_aleph]
  have hac := almostDisjointnessNumber_le_continuum ha
  exact ⟨htwo, hthree, hac, hthree.trans hac⟩

end Roitman

