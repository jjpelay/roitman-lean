import Roitman.RecetaB.Defs
import Roitman.RecetaB.Tower
import Roitman.PrefixNoCover

/-!
# Recipe B: one stage of the recursion

Lemmas 3.2 and 3.3 of arXiv:2610.00639, together with the limit
step (pseudo-intersections of the reservation towers).
-/

noncomputable section
namespace Roitman.RecetaB
open Roitman Bookkeeping

/-- Finitely many reservations of an earlier segment of the tower of `α`
have infinite intersection. -/
theorem tower_finite_inter {d : I → ℕ → ℕ} {ξ α : I} {f : I → StageValue}
    (hprev : ∀ η, η < ξ → GoodB d η f) (u : Finset I)
    (hu : ∀ η ∈ u, α ≤ η ∧ η < ξ) :
    {i | ∀ η ∈ u, i ∈ (f η).2 α}.Infinite := by
  classical
  by_cases hne : u.Nonempty
  · let m := u.max' hne
    have hm := hu m (u.max'_mem hne)
    have hinf : ((f m).2 α).Infinite := (hprev m hm.2).2.2.1 α hm.1
    have hfin : (⋃ η ∈ u, ((f m).2 α \ (f η).2 α)).Finite := by
      apply u.finite_toSet.biUnion
      intro η hη
      have hle : η ≤ m := u.le_max' η hη
      rcases eq_or_lt_of_le hle with heq | hlt
      · rw [heq, Set.sdiff_self]
        exact Set.finite_empty
      · exact (hprev m hm.2).2.2.2.1 α η (hu η hη).1 hlt
    apply (hinf.sdiff hfin).mono
    rintro i ⟨hi, hnot⟩ η hη
    by_contra hiη
    exact hnot (Set.mem_biUnion hη ⟨hi, hiη⟩)
  · have hu' : u = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst hu'
    simpa using (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)

/-- The limit step: an infinite set almost contained in every earlier
reservation for `α`. -/
theorem exists_reservation {d : I → ℕ → ℕ} {ξ α : I} {f : I → StageValue}
    (hprev : ∀ η, η < ξ → GoodB d η f) :
    ∃ P : Set ℕ, P.Infinite ∧ ∀ η, α ≤ η → η < ξ → (P \ (f η).2 α).Finite := by
  classical
  let s : ℕ → Set ℕ := fun k =>
    {i | ∀ η, enumEarlier ξ k = some η → α ≤ η → i ∈ (f η).2 α}
  have hs : ∀ k, {i | ∀ m ≤ k, i ∈ s m}.Infinite := by
    intro k
    let u : Finset I := (prefixIndices ξ k).filter (fun η => α ≤ η)
    have hu : ∀ η ∈ u, α ≤ η ∧ η < ξ := by
      intro η hη
      obtain ⟨hη1, hη2⟩ := Finset.mem_filter.mp hη
      exact ⟨hη2, prefixIndices_lt hη1⟩
    apply (tower_finite_inter hprev u hu).mono
    intro i hi
    show ∀ m ≤ k, ∀ η, enumEarlier ξ m = some η → α ≤ η → i ∈ (f η).2 α
    intro m hm η he hαη
    exact hi η (Finset.mem_filter.mpr ⟨mem_prefixIndices.mpr ⟨m, hm, he⟩, hαη⟩)
  obtain ⟨P, hP, hPs⟩ := exists_pseudoIntersection s hs
  refine ⟨P, hP, ?_⟩
  intro η hαη hη
  obtain ⟨k, hk⟩ := enumEarlier_complete hη
  apply (hPs k).subset
  rintro i ⟨hiP, hiη⟩
  exact ⟨hiP, fun hs' => hiη (hs' η hk hαη)⟩

/-- One stage of recipe B (Lemma 3.3). -/
theorem goodB_extension (d : I → ℕ → ℕ) (hd : ∀ α n, n ≤ d α n)
    (ξ : I) (f : I → StageValue) (hprev : ∀ η, η < ξ → GoodB d η f) :
    ∃ v, GoodB d ξ (Function.update f ξ v) := by
  classical
  -- the reservations available at stage `ξ`
  have hN : ∀ r : Set.Iic ξ, ∃ P : Set ℕ, P.Infinite ∧
      ∀ η, r.val ≤ η → η < ξ → (P \ (f η).2 r.val).Finite :=
    fun _ => exists_reservation hprev
  choose N hNinf hNsub using hN
  have hα0ξ : (task ξ).1 ≤ ξ := task_fst_le ξ
  let J0 : Set ℕ := {j | j ∈ N ⟨(task ξ).1, hα0ξ⟩ ∧
    (stageClass d f ξ ∩ interval (d (task ξ).1) j).Nonempty}
  -- the parameters of the stage: the class of `task ξ`, or a harmless default
  obtain ⟨α, G, J, hαξ, hJN, hJ, hJG, hold, hcase⟩ :
      ∃ (α : I) (G J : Set ℕ) (hαξ : α ≤ ξ),
        J ⊆ N ⟨α, hαξ⟩ ∧ J.Infinite ∧
        (∀ j ∈ J, (G ∩ interval (d α) j).Nonempty) ∧
        (∀ η, η < α → (G ∩ (f η).1).Finite) ∧
        (J0.Infinite → α = (task ξ).1 ∧ G = stageClass d f ξ) := by
    by_cases hJ0 : J0.Infinite
    · refine ⟨(task ξ).1, stageClass d f ξ, J0, hα0ξ, fun j hj => hj.1, hJ0,
        fun j hj => hj.2, ?_, fun _ => ⟨rfl, rfl⟩⟩
      intro η hη
      obtain ⟨k, hk⟩ := enumEarlier_complete hη
      have hfin := traceSet_inter_finite (earlier (members f) (task ξ).1) (d (task ξ).2) k
      have he : earlier (members f) (task ξ).1 k = (f η).1 := by
        simp [earlier, hk, members]
      rw [he] at hfin
      exact hfin
    · have : Nonempty (Set.Iic ξ) := ⟨⟨ξ, le_refl ξ⟩⟩
      refine ⟨⊥, Set.univ, N ⟨⊥, (bot_le : ⊥ ≤ ξ)⟩, bot_le, subset_rfl, hNinf _, ?_, ?_,
        fun h => absurd h hJ0⟩
      · intro j _
        simpa using interval_nonempty (hd ⊥) j
      · intro η hη
        exact absurd hη not_lt_bot
  have : Nonempty (Set.Iic ξ) := ⟨⟨ξ, le_refl ξ⟩⟩
  obtain ⟨jseq, S, hjinj, hjJ, hSN, hSinf, hSdisj⟩ :=
    reservationStage (d α) (hd α) J hJ (Set.Iic ξ) (fun r => d r.val)
      (fun r => hd r.val) N hNinf
  let a : Set ℕ := {x | x ∈ G ∧ ∃ n, x ∈ interval (d α) (jseq n)}
  let Snew : I → Set ℕ := fun γ => if hγ : γ ≤ ξ then S ⟨γ, hγ⟩ else ∅
  refine ⟨(a, Snew), ?_⟩
  have hself : Function.update f ξ (a, Snew) ξ = (a, Snew) := Function.update_self _ _ _
  have hupd : ∀ η, η < ξ → Function.update f ξ (a, Snew) η = f η :=
    fun η hη => Function.update_of_ne hη.ne _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the new member is infinite
    rw [hself]
    apply Set.infinite_of_forall_exists_gt
    intro M
    obtain ⟨j, ⟨n, rfl⟩, hj⟩ := (Set.infinite_range_of_injective hjinj).exists_gt M
    obtain ⟨x, hxG, hxI⟩ := hJG _ (hjJ n)
    exact ⟨x, ⟨hxG, n, hxI⟩, lt_of_lt_of_le hj ((le_h (hd α) _).trans hxI.1)⟩
  · -- almost disjointness from the earlier members
    intro η hη
    rw [hself, hupd η hη]
    by_cases hηα : η < α
    · exact (hold η hηα).subset (fun x hx => ⟨hx.1.1, hx.2⟩)
    · have hαη : α ≤ η := not_lt.mp hηα
      have hdiff : (N ⟨α, hαξ⟩ \ (f η).2 α).Finite := hNsub ⟨α, hαξ⟩ η hαη hη
      have hF : {n | jseq n ∉ (f η).2 α}.Finite := by
        apply (hdiff.preimage (fun _ _ _ _ h => hjinj h)).subset
        intro n hn
        exact ⟨hJN (hjJ n), hn⟩
      apply (hF.biUnion (fun n _ => interval_finite (d α) (jseq n))).subset
      rintro x ⟨⟨_, n, hxn⟩, hxη⟩
      refine Set.mem_biUnion (x := n) ?_ hxn
      intro hn
      have hdisj := (hprev η hη).2.2.2.2.1 α hαη (jseq n) hn
      exact Set.disjoint_left.mp hdisj hxη hxn
  · -- the new reservations are infinite
    intro γ hγ
    rw [hself]
    show (Snew γ).Infinite
    simp only [Snew, hγ, ↓reduceDIte]
    exact hSinf _
  · -- the towers decrease modulo finite sets
    intro γ η hγη hη
    rw [hself, hupd η hη]
    have hγ : γ ≤ ξ := hγη.trans hη.le
    show (Snew γ \ (f η).2 γ).Finite
    simp only [Snew, hγ, ↓reduceDIte]
    exact (hNsub ⟨γ, hγ⟩ η hγη hη).subset (Set.sdiff_subset_sdiff_left (hSN _))
  · -- the new member misses the new reserved intervals
    intro γ hγ j hj
    rw [hself] at hj ⊢
    change j ∈ Snew γ at hj
    simp only [Snew, hγ, ↓reduceDIte] at hj
    apply Set.disjoint_left.mpr
    rintro x ⟨_, n, hxn⟩ hxj
    exact Set.disjoint_left.mp (hSdisj ⟨γ, hγ⟩ j hj n) hxn hxj
  · -- the capture property of the assigned class
    intro hbad
    rw [stageClass_congr hupd, hself] at *
    have hJ0 : J0.Infinite := by
      have hbig := (hNinf ⟨(task ξ).1, hα0ξ⟩).sdiff hbad
      apply hbig.mono
      rintro j ⟨hjN, hjbad⟩
      refine ⟨hjN, ?_⟩
      by_contra hne
      exact hjbad hne
    obtain ⟨hαeq, hGeq⟩ := hcase hJ0
    apply (Set.infinite_range_of_injective hjinj).mono
    rintro _ ⟨n, rfl⟩ x ⟨hxG, hxI⟩
    rw [← hGeq] at hxG
    rw [← hαeq] at hxI
    exact ⟨hxG, n, hxI⟩

end Roitman.RecetaB
