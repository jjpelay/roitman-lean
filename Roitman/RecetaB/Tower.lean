import Roitman.Basic
import Roitman.Bookkeeping

/-!
# Pseudo-intersections and the single-stage choice of recipe B

`exists_pseudoIntersection` is the limit step of the reservation towers.
`reservationStage` is the diagonal choice inside one stage: whole blocks for
the new member, interleaved with fresh reserved intervals for countably many
partitions.
-/

namespace Roitman.RecetaB
open Roitman

/-- A sequence of sets whose finite intersections are infinite has an infinite
pseudo-intersection. -/
theorem exists_pseudoIntersection (s : ℕ → Set ℕ)
    (hs : ∀ k, {i | ∀ m ≤ k, i ∈ s m}.Infinite) :
    ∃ P : Set ℕ, P.Infinite ∧ ∀ m, (P \ s m).Finite := by
  classical
  have hp : ∀ k, ∃ p, k ≤ p ∧ ∀ m ≤ k, p ∈ s m := by
    intro k
    obtain ⟨p, hp, hkp⟩ := (hs k).exists_gt k
    exact ⟨p, hkp.le, hp⟩
  choose p hpk hps using hp
  refine ⟨Set.range p, ?_, ?_⟩
  · apply Set.infinite_of_forall_exists_gt
    intro N
    exact ⟨p (N + 1), ⟨N + 1, rfl⟩, by have := hpk (N + 1); omega⟩
  · intro m
    apply ((Set.finite_lt_nat m).image p).subset
    rintro _ ⟨⟨k, rfl⟩, hk⟩
    refine ⟨k, ?_, rfl⟩
    by_contra hkm
    exact hk (hps k m (by simp only [Set.mem_ofPred_eq, not_lt] at hkm; exact hkm))

/-- The diagonal choice of one stage of recipe B.  The blocks `I^{d0}_{j_n}`
come from `J`; the reserved indices for the partition `dr r` come from `N r`;
every chosen block lies strictly between consecutive reserved intervals. -/
theorem reservationStage
    (d0 : ℕ → ℕ) (hd0 : ∀ n, n ≤ d0 n) (J : Set ℕ) (hJ : J.Infinite)
    (R : Type*) [Countable R] [Nonempty R]
    (dr : R → ℕ → ℕ) (hdr : ∀ r n, n ≤ dr r n)
    (N : R → Set ℕ) (hN : ∀ r, (N r).Infinite) :
    ∃ (jseq : ℕ → ℕ) (S : R → Set ℕ),
      Function.Injective jseq ∧ (∀ n, jseq n ∈ J) ∧
      (∀ r, S r ⊆ N r) ∧ (∀ r, (S r).Infinite) ∧
      (∀ r, ∀ i ∈ S r, ∀ n, Disjoint (interval d0 (jseq n)) (interval (dr r) i)) := by
  classical
  have hJex : ∀ b, ∃ j ∈ J, b ≤ h d0 j := by
    intro b
    obtain ⟨j, hj, hbj⟩ := hJ.exists_gt b
    exact ⟨j, hj, hbj.le.trans (le_h hd0 j)⟩
  choose jf hjfJ hjf using hJex
  have hNex : ∀ r b, ∃ i ∈ N r, b ≤ h (dr r) i := by
    intro r b
    obtain ⟨i, hi, hbi⟩ := (hN r).exists_gt b
    exact ⟨i, hi, hbi.le.trans (le_h (hdr r) i)⟩
  choose ifn hifN hif using hNex
  let γ : ℕ → R := Bookkeeping.fairSchedule R
  let bseq : ℕ → ℕ := fun n =>
    Nat.rec 0 (fun n b => h (dr (γ n)) (ifn (γ n) (h d0 (jf b + 1)) + 1)) n
  let jseq : ℕ → ℕ := fun n => jf (bseq n)
  let iseq : ℕ → ℕ := fun n => ifn (γ n) (h d0 (jseq n + 1))
  have hb0 : ∀ n, bseq n ≤ h d0 (jseq n) := fun n => hjf (bseq n)
  have hb1 : ∀ n, h d0 (jseq n + 1) ≤ h (dr (γ n)) (iseq n) := fun n => hif _ _
  have hb2 : ∀ n, bseq (n + 1) = h (dr (γ n)) (iseq n + 1) := fun n => rfl
  have hstep : ∀ n, h (dr (γ n)) (iseq n) < bseq (n + 1) := by
    intro n
    rw [hb2]
    exact h_strictMono (hdr (γ n)) (Nat.lt_succ_self _)
  have hjstep : ∀ n, h d0 (jseq n) < h d0 (jseq n + 1) :=
    fun n => h_strictMono hd0 (Nat.lt_succ_self _)
  have hbsucc : ∀ n, bseq n < bseq (n + 1) := by
    intro n
    have := hb0 n
    have := hjstep n
    have := hb1 n
    have := hstep n
    omega
  have hbmono : StrictMono bseq := strictMono_nat_of_lt_succ hbsucc
  -- every point of the `n`-th block lies in `[bseq n, h (dr (γ n)) (iseq n))`
  have hblock : ∀ n x, x ∈ interval d0 (jseq n) →
      bseq n ≤ x ∧ x < h d0 (jseq n + 1) := by
    intro n x hx
    exact ⟨(hb0 n).trans hx.1, hx.2⟩
  -- every point of the `m`-th reserved interval lies in
  -- `[h d0 (jseq m + 1), bseq (m + 1))`
  have hres : ∀ m y, y ∈ interval (dr (γ m)) (iseq m) →
      h d0 (jseq m + 1) ≤ y ∧ y < bseq (m + 1) := by
    intro m y hy
    exact ⟨(hb1 m).trans hy.1, by rw [hb2]; exact hy.2⟩
  have hdisj : ∀ m n, Disjoint (interval d0 (jseq n)) (interval (dr (γ m)) (iseq m)) := by
    intro m n
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨hx1, hx2⟩ := hblock n x hx
    obtain ⟨hy1, hy2⟩ := hres m x hy
    rcases lt_trichotomy n m with hnm | rfl | hmn
    · have h1 : bseq (n + 1) ≤ bseq m := hbmono.monotone hnm
      have h2 := hstep n
      have h3 := hb1 n
      have h4 := hb0 m
      have h5 := hjstep m
      omega
    · omega
    · have h1 : bseq (m + 1) ≤ bseq n := hbmono.monotone hmn
      omega
  refine ⟨jseq, fun r => iseq '' {n | γ n = r}, ?_, fun n => hjfJ _, ?_, ?_, ?_⟩
  · intro n m hnm
    by_contra hne
    have key : ∀ n m, n < m → jseq n ≠ jseq m := by
      intro n m hlt heq
      have h1 : bseq (n + 1) ≤ bseq m := hbmono.monotone hlt
      have h2 := hb0 m
      have h3 := hb1 n
      have h4 := hstep n
      rw [heq] at h3
      have h5 := hjstep m
      omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact key n m hlt hnm
    · exact key m n hgt hnm.symm
  · rintro r _ ⟨n, hn, rfl⟩
    simp only [Set.mem_ofPred_eq] at hn
    rw [← hn]
    exact hifN _ _
  · intro r
    apply (Bookkeeping.fairSchedule_infinite R r).image
    intro n hn m hm heq
    simp only [Set.mem_ofPred_eq] at hn hm
    by_contra hne
    have key : ∀ n m, γ n = r → γ m = r → n < m → iseq n ≠ iseq m := by
      intro n m hn hm hlt heq
      have h1 : bseq (n + 1) ≤ bseq m := hbmono.monotone hlt
      have h2 := hstep n
      have h3 := hb1 m
      have h4 := hb0 m
      have h5 := hjstep m
      rw [hn, heq, ← hm] at h2
      omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact key n m hn hm hlt heq
    · exact key m n hm hn hgt heq.symm
  · rintro r _ ⟨m, hm, rfl⟩ n
    simp only [Set.mem_ofPred_eq] at hm
    rw [← hm]
    exact hdisj m n

end Roitman.RecetaB
