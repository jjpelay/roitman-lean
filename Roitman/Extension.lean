import Roitman.ConstructionSupport
import Roitman.CaptureStage
import Roitman.PrefixNoCover

noncomputable section
namespace Roitman
open Bookkeeping

abbrev GapRequirement (ξ : I) := Set.Iic ξ × Finset (Set.Iio ξ)

instance (ξ : I) : Nonempty (GapRequirement ξ) := ⟨(⟨ξ, by exact le_refl ξ⟩, ∅)⟩

def reqIndices {ξ : I} (r : GapRequirement ξ) : Finset I := by
  classical
  exact (r.2.filter (fun η => r.1.val ≤ η.val)).image Subtype.val

theorem reqIndices_bounds {ξ : I} (r : GapRequirement ξ) {η : I}
    (h : η ∈ reqIndices r) : r.1.val ≤ η ∧ η < ξ := by
  classical
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
  exact ⟨(Finset.mem_filter.mp he).2, e.property⟩

def unionMembers (A : I → Set ℕ) (u : Finset I) : Set ℕ :=
  {i | ∃ η ∈ u, i ∈ A η}

theorem unionMembers_disjoint {A : I → Set ℕ} {u : Finset I} {z : Set ℕ} :
    Disjoint (unionMembers A u) z ↔ ∀ η ∈ u, Disjoint (A η) z := by
  constructor
  · intro h η hη
    exact Set.disjoint_left.mpr (fun _ hi hiz => Set.disjoint_left.mp h ⟨η, hη, hi⟩ hiz)
  · intro h
    apply Set.disjoint_left.mpr
    rintro i ⟨η, hη, hi⟩ hiz
    exact Set.disjoint_left.mp (h η hη) hi hiz

theorem reqIndices_realize {ξ γ : I} (hγ : γ ≤ ξ) (u : Finset I)
    (hu : ∀ η ∈ u, γ ≤ η ∧ η < ξ) :
    ∃ r : GapRequirement ξ, r.1.val = γ ∧ reqIndices r = u := by
  classical
  refine ⟨(⟨γ, hγ⟩, u.subtype (fun η => η < ξ)), rfl, ?_⟩
  ext η
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_subtype.mp (Finset.mem_filter.mp he).1
  · intro h
    have hb := hu η h
    exact Finset.mem_image.mpr ⟨⟨η, hb.2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_subtype.mpr h, hb.1⟩, rfl⟩

theorem goodAt_extension (d : I → ℕ → ℕ) (hd : ∀ α n, n ≤ d α n)
    (ξ : I) (A : I → Set ℕ) (hprev : ∀ η, η < ξ → GoodAt d task η A) :
    ∃ a, GoodAt d task ξ (Function.update A ξ a) := by
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
  obtain ⟨a, ha, had, hcap, hpres⟩ := captureStage
    (d (task ξ).1) (traceClass d A (task ξ).1 (task ξ).2) (earlier A ξ) ds old
    (fun r n => hd (e r).1.val n)
    (prefix_noCover d hd A ξ (task ξ).1 (task ξ).2 (task_fst_le ξ) hg)
    (prefix_escape d hd A ξ hg) hold
  refine ⟨a, ?_⟩
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

end Roitman


