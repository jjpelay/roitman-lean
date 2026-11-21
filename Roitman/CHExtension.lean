import Roitman.Extension
import Roitman.CHSupport
import Roitman.CaptureStageCH

noncomputable section
namespace Roitman
open Bookkeeping

private theorem positive_goodAtCH_extension (d : I → ℕ → ℕ) (hd : ∀ α n, n ≤ d α n)
    (X : I → Set (Finset ℕ)) (ξ : I) (A : I → Set ℕ)
    (hprev : ∀ η, η < ξ → GoodAt d task η A)
    (hpos : PositiveBefore ξ A (X ξ)) :
    ∃ a, GoodAtCH d X ξ (Function.update A ξ a) := by
  classical
  have hg : ∀ γ, γ ≤ ξ → ∀ u : Finset I,
      (∀ η ∈ u, γ ≤ η ∧ η < ξ) → (gapIndices d A γ u).Infinite := by
    intro γ _ u hu
    exact gaps_before hprev γ u hu
  let e : ℕ → GapRequirement ξ := enumerate (GapRequirement ξ)
  have he : Function.Surjective e := enumerate_surjective _
  let ds : ℕ → ℕ → ℕ := fun n => d (e n).1.val
  let old : ℕ → Set ℕ := fun n => unionMembers A (reqIndices (e n))
  have hold : ∀ r, {j | Disjoint (old r) (interval (ds r) j)}.Infinite := by
    intro r
    have hi := hg (e r).1.val (e r).1.property (reqIndices (e r))
      (fun η hη => reqIndices_bounds (e r) hη)
    simpa only [old, ds, unionMembers_disjoint, gapIndices] using hi
  have hpositive : ∀ n b, ∃ t ∈ X ξ, t.Nonempty ∧
      ∀ i ∈ t, i ∉ exclusions (earlier A ξ) n b := by
    intro n b
    obtain ⟨t, ht, hne, hav⟩ := hpos (prefixIndices ξ n)
      (fun η hη => prefixIndices_lt hη) b
    refine ⟨t, ht, hne, ?_⟩
    intro i hi hiE
    rcases exclusions_subset_prefix A ξ n b hiE with hib | him
    · exact (not_lt_of_ge (hav i hi).1) hib
    · obtain ⟨η, hη, hiη⟩ := mem_memberUnion.mp him
      exact (hav i hi).2 η hη hiη
  obtain ⟨a, ha, had, hcap, hpres, hX⟩ := captureStageCH
    (d (task ξ).1) (traceClass d A (task ξ).1 (task ξ).2) (earlier A ξ) ds old (X ξ)
    (fun r n => hd (e r).1.val n)
    (prefix_noCover d hd A ξ (task ξ).1 (task ξ).2 (task_fst_le ξ) hg)
    (prefix_escape d hd A ξ hg) hold hpositive
  refine ⟨a, ?_, ?_⟩
  swap
  · intro _
    simpa only [Captured, Function.update_self] using hX
  refine ⟨by simpa using ha, ?_, ?_, ?_⟩
  · intro η hη
    obtain ⟨k, hk⟩ := enumEarlier_complete hη
    have hadk := had k
    simpa [earlier, hk, Function.update_of_ne hη.ne] using hadk
  · intro γ hγ u hu
    let v := u.erase ξ
    have hv : ∀ η ∈ v, γ ≤ η ∧ η < ξ := by
      intro η hη
      have hm := Finset.mem_erase.mp hη
      exact ⟨(hu η hm.2).1, lt_of_le_of_ne (hu η hm.2).2 hm.1⟩
    obtain ⟨r, hrγ, hrv⟩ := reqIndices_realize hγ v hv
    obtain ⟨n, hn⟩ := he r
    have hp := hpres n
    apply hp.mono
    intro j hj η hη
    apply Set.disjoint_left.mpr
    intro i hi hii
    have hmem : i ∈ old n ∪ a := by
      by_cases heq : η = ξ
      · subst η
        exact Or.inr (by simpa using hi)
      · apply Or.inl
        have hiv : η ∈ reqIndices (e n) := by
          rw [hn, hrv]
          exact Finset.mem_erase.mpr ⟨heq, hη⟩
        exact ⟨η, hiv, by simpa [Function.update_of_ne heq] using hi⟩
    exact Set.disjoint_left.mp hj hmem (by simpa only [ds, hn, hrγ] using hii)
  · intro x hx hxG
    simp only [Function.update_self]
    apply hcap x hx
    have heq : traceClass d (Function.update A ξ a) (task ξ).1 (task ξ).2 =
        traceClass d A (task ξ).1 (task ξ).2 := by
      apply traceClass_congr
      intro η hη
      exact Function.update_of_ne (lt_of_lt_of_le hη (task_fst_le ξ)).ne _ _
    rwa [heq] at hxG

theorem goodAtCH_extension (d : I → ℕ → ℕ) (hd : ∀ α n, n ≤ d α n)
    (X : I → Set (Finset ℕ)) (ξ : I) (A : I → Set ℕ)
    (hprev : ∀ η, η < ξ → GoodAtCH d X η A) :
    ∃ a, GoodAtCH d X ξ (Function.update A ξ a) := by
  classical
  by_cases hpos : PositiveBefore ξ A (X ξ)
  · exact positive_goodAtCH_extension d hd X ξ A (fun η hη => (hprev η hη).1) hpos
  · obtain ⟨a, ha⟩ := goodAt_extension d hd ξ A (fun η hη => (hprev η hη).1)
    refine ⟨a, ha, ?_⟩
    intro hp
    apply False.elim
    apply hpos
    apply (positiveBefore_congr (A := Function.update A ξ a) (B := A) ?_).mp hp
    intro η hη
    exact Function.update_of_ne hη.ne _ _

end Roitman




