import Roitman.RecetaB.Main
import Roitman.RecetaB.Closure
import Roitman.CHSupport

/-!
# Recipe B: almost strong separability from `𝔡 = ℵ₁`

Theorem 5.1 of arXiv:2610.00639: without CH, the family of recipe B
is almost strongly separable, provided the sequence also dominates a scale.
The definitions `Positive`, `Captured` and `AlmostStronglySeparable` are those
of the original CH refinement (`Roitman/CHSupport.lean`).

The manuscript reindexes the dominating family so that it is itself
`≤*`-increasing. Here we use instead `d α = max (normalized α) (s α)` for a
scale `s`: the normalized part gives pointwise domination and the scale gives
the monotonicity needed at the closure point. The argument is otherwise the
same.
-/

noncomputable section
namespace Roitman.RecetaB
open Roitman Bookkeeping

/-- Eventual domination. -/
def EvLE (g h : ℕ → ℕ) : Prop := ∃ N, ∀ n, N ≤ n → g n ≤ h n

theorem EvLE.trans {f g h : ℕ → ℕ} (h₁ : EvLE f g) (h₂ : EvLE g h) : EvLE f h := by
  obtain ⟨N₁, h₁⟩ := h₁
  obtain ⟨N₂, h₂⟩ := h₂
  exact ⟨max N₁ N₂, fun n hn =>
    (h₁ n (le_of_max_le_left hn)).trans (h₂ n (le_of_max_le_right hn))⟩

/-- Countably many functions are eventually bounded by one function. -/
theorem exists_evBound (g : ℕ → ℕ → ℕ) : ∃ b : ℕ → ℕ, ∀ k, EvLE (g k) b :=
  ⟨fun n => (Finset.range (n + 1)).sup (fun k => g k n),
    fun k => ⟨k, fun n hn =>
      Finset.le_sup (f := fun k => g k n) (Finset.mem_range.mpr (by omega))⟩⟩

/-- A `≤*`-increasing sequence of length `ω₁` above a given sequence. -/
theorem exists_scale (D : I → ℕ → ℕ) :
    ∃ s : I → ℕ → ℕ, (∀ ν, EvLE (D ν) (s ν)) ∧ (∀ μ ν, μ < ν → EvLE (s μ) (s ν)) := by
  obtain ⟨s, hs⟩ := local_recursion (ι := I) (X := ℕ → ℕ)
    (fun ν s => EvLE (D ν) (s ν) ∧ ∀ μ, μ < ν → EvLE (s μ) (s ν))
    (by
      intro ν f g h
      rw [h ν le_rfl]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun μ hμ => by rw [← h μ hμ.le]; exact h2 μ hμ⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun μ hμ => by rw [h μ hμ.le]; exact h2 μ hμ⟩)
    (by
      intro ν f _
      let g : ℕ → ℕ → ℕ := fun k n =>
        max (D ν n) ((enumEarlier ν k).elim 0 (fun μ => f μ n))
      obtain ⟨b, hb⟩ := exists_evBound g
      refine ⟨b, ?_, ?_⟩
      · simp only [Function.update_self]
        exact EvLE.trans ⟨0, fun n _ => le_max_left _ _⟩ (hb 0)
      · intro μ hμ
        simp only [Function.update_self, Function.update_of_ne hμ.ne]
        obtain ⟨k, hk⟩ := enumEarlier_complete hμ
        refine EvLE.trans ⟨0, fun n _ => ?_⟩ (hb k)
        simp only [g, hk, Option.elim_some]
        exact le_max_right _ _)
  exact ⟨s, fun ν => (hs ν).1, fun μ ν h => (hs ν).2 μ h⟩

/-- Theorem 5.1 of recipe B, combinatorial part. -/
theorem goodB_almostStronglySeparable {d : I → ℕ → ℕ} (hd : ∀ α n, n ≤ d α n)
    (hdom : PointwiseDominating d) {s : I → ℕ → ℕ}
    (hs_dom : ∀ g : ℕ → ℕ, ∃ ν, EvLE g (s ν))
    (hs_mono : ∀ μ ν, μ < ν → EvLE (s μ) (s ν))
    (hsd : ∀ α n, s α n ≤ d α n)
    {f : I → StageValue} (hf : ∀ ξ, GoodB d ξ f) :
    AlmostStronglySeparable (members f) := by
  classical
  intro X hX
  -- witnesses in `X` avoiding finitely many members and a finite initial segment
  choose w hwX hwne hw using hX
  let E : Finset I → ℕ → ℕ := fun u m => (w u m).sup id
  -- `F γ` bounds the witnesses for all finite sets of indices below `γ`
  have hF : ∀ γ : I, ∃ ν, ∀ u : Finset I, (∀ η ∈ u, η ≤ γ) → EvLE (E u) (s ν) := by
    intro γ
    let U : ℕ → Finset I := fun k =>
      (enumerate (Finset (Set.Iic γ)) k).map (Function.Embedding.subtype _)
    obtain ⟨b, hb⟩ := exists_evBound (fun k => E (U k))
    obtain ⟨ν, hν⟩ := hs_dom b
    refine ⟨ν, fun u hu => ?_⟩
    obtain ⟨k, hk⟩ :=
      enumerate_surjective (Finset (Set.Iic γ)) (u.subtype (· ∈ Set.Iic γ))
    have hUk : U k = u := by
      simp only [U, hk]
      rw [Finset.subtype_map]
      exact Finset.filter_true_of_mem (fun η hη => Set.mem_Iic.mpr (hu η hη))
    rw [← hUk]
    exact (hb k).trans hν
  choose F hFspec using hF
  -- a closure point
  obtain ⟨δ, hδbot, hδ⟩ := exists_closed F
  let P : ℕ → Finset I := fun k => prefixIndices δ k
  have hPd : ∀ k, EvLE (E (P k)) (d δ) := by
    intro k
    let γ : I := (P k).sup id
    have hγδ : γ < δ := (Finset.sup_lt_iff hδbot).mpr (fun η hη => prefixIndices_lt hη)
    have h1 := hFspec γ (P k) (fun η hη => Finset.le_sup (f := id) hη)
    exact (h1.trans (hs_mono _ _ (hδ γ hγδ))).trans ⟨0, fun n _ => hsd δ n⟩
  choose t ht using hPd
  -- increasing thresholds
  let t' : ℕ → ℕ := fun k => (Finset.range (k + 1)).sup t + k
  have ht_le : ∀ k, t k ≤ t' k := fun k =>
    (Finset.le_sup (f := t) (Finset.mem_range.mpr (Nat.lt_succ_self k))).trans
      (Nat.le_add_right _ _)
  have hk_le : ∀ k, k ≤ t' k := fun k => Nat.le_add_left _ _
  -- the number of old members to avoid in the block `j`
  let H : ℕ → ℕ := fun j => h (d δ) j
  let κ : ℕ → ℕ := fun j => Nat.findGreatest (fun k => t' k ≤ H j) (H j)
  have hκ_spec : ∀ j, t' 0 ≤ H j → t' (κ j) ≤ H j :=
    fun j hj => Nat.findGreatest_spec (P := fun k => t' k ≤ H j) (Nat.zero_le _) hj
  have hκ_ge : ∀ j k, t' k ≤ H j → k ≤ κ j :=
    fun j k hk => Nat.le_findGreatest ((hk_le k).trans hk) hk
  -- the witness in the block `j`
  let sw : ℕ → Finset ℕ := fun j => w (P (κ j)) (H j)
  have hsw_interval : ∀ j, t' 0 ≤ H j → (↑(sw j) : Set ℕ) ⊆ interval (d δ) j := by
    intro j hj i hi
    have hlow := (hw (P (κ j)) (H j) i hi).1
    have hup : i ≤ E (P (κ j)) (H j) := Finset.le_sup (f := id) hi
    have hE := ht (κ j) (H j) ((ht_le (κ j)).trans (hκ_spec j hj))
    refine ⟨hlow, ?_⟩
    simp only [h_succ]
    exact Nat.lt_succ_of_le (hup.trans hE)
  have hsw_avoid : ∀ j, ∀ i ∈ sw j, ∀ k ≤ κ j, i ∉ earlier (members f) δ k := by
    intro j i hi k hk
    cases he : enumEarlier δ k with
    | none => simp [earlier, he]
    | some η =>
      simp only [earlier, he, Option.elim_some]
      exact (hw (P (κ j)) (H j) i hi).2 η (mem_prefixIndices.mpr ⟨k, hk, he⟩)
  -- a trace bound for all witnesses
  let g : ℕ → ℕ := fun k => (Finset.range (t' k)).sup (fun j => (sw j).sup id + 1)
  have hsw_trace : ∀ j, (↑(sw j) : Set ℕ) ⊆ traceSet (earlier (members f) δ) g := by
    intro j i hi k hik
    by_cases hk : k ≤ κ j
    · exact absurd hik (hsw_avoid j i hi k hk)
    · have hjk : j < t' k := by
        by_contra hjk
        exact hk (hκ_ge j k ((not_lt.mp hjk).trans' (le_refl _) |>.trans
          (le_h (hd δ) j)))
      have hi' : i ≤ (sw j).sup id := Finset.le_sup (f := id) hi
      have hj' : (sw j).sup id + 1 ≤ g k :=
        Finset.le_sup (f := fun j => (sw j).sup id + 1) (Finset.mem_range.mpr hjk)
      omega
  obtain ⟨β, hβ⟩ := hdom g
  let G := traceClass d (members f) δ β
  have hswG : ∀ j, (↑(sw j) : Set ℕ) ⊆ G :=
    fun j => (hsw_trace j).trans (traceSet_mono hβ)
  -- the stage assigned to `(δ, β)`
  have h6 := (hf (gamma (δ, β))).2.2.2.2.2
  simp only [stageClass, task_gamma] at h6
  have hbad : {j | ¬ (G ∩ interval (d δ) j).Nonempty}.Finite := by
    apply (Set.finite_lt_nat (t' 0)).subset
    intro j hj
    by_contra hlt
    have hj0 : t' 0 ≤ H j := (not_lt.mp hlt).trans (le_h (hd δ) j)
    obtain ⟨i, hi⟩ := hwne (P (κ j)) (H j)
    exact hj ⟨i, hswG j hi, hsw_interval j hj0 hi⟩
  have hT := h6 hbad
  refine ⟨gamma (δ, β), ?_⟩
  have hT' : ({j | G ∩ interval (d δ) j ⊆ (f (gamma (δ, β))).1} \
      {j | j < t' 0}).Infinite := hT.sdiff (Set.finite_lt_nat _)
  apply (hT'.image ?_).mono
  · rintro _ ⟨j, ⟨hjT, hj⟩, rfl⟩
    have hj0 : t' 0 ≤ H j := (not_lt.mp hj).trans (le_h (hd δ) j)
    exact ⟨hwX _ _, fun i hi => hjT ⟨hswG j hi, hsw_interval j hj0 hi⟩⟩
  · rintro j ⟨_, hj⟩ j' ⟨_, hj'⟩ heq
    have hj0 : t' 0 ≤ H j := (not_lt.mp hj).trans (le_h (hd δ) j)
    have hj0' : t' 0 ≤ H j' := (not_lt.mp hj').trans (le_h (hd δ) j')
    obtain ⟨i, hi⟩ := hwne (P (κ j)) (H j)
    have hi' : i ∈ sw j' := by
      change sw j = sw j' at heq
      rw [← heq]
      exact hi
    by_contra hne
    exact Set.disjoint_left.mp (intervals_disjoint (hd δ) hne)
      (hsw_interval j hj0 hi) (hsw_interval j' hj0' hi')

/-- Theorem 5.1 of recipe B: if `𝔡 = ℵ₁`, there is an almost strongly separable
MAD family of size `ℵ₁`. No CH is assumed. -/
theorem d_eq_aleph_one_implies_almostStronglySeparable_MAD
    (hd : IsDominatingNumber (Cardinal.aleph 1)) :
    ∃ A : I → Set ℕ, MADFamily A ∧
      Cardinal.mk (Set.range A) = Cardinal.aleph 1 ∧ AlmostStronglySeparable A := by
  obtain ⟨F, hF, hcard⟩ := hd.1
  obtain ⟨D, hD⟩ := dominatingSet_indexed hF hcard
  obtain ⟨s, hsD, hs_mono⟩ := exists_scale D
  let d : I → ℕ → ℕ := fun α n => max (normalizedI D α n) (s α n)
  have hd' : ∀ α n, n ≤ d α n := fun α n => (normalizedI_ge_id D α n).trans (le_max_left _ _)
  have hdom : PointwiseDominating d := by
    intro g
    obtain ⟨α, hα⟩ := normalizedI_pointwise hD g
    exact ⟨α, fun n => (hα n).trans (le_max_left _ _)⟩
  have hs_dom : ∀ g : ℕ → ℕ, ∃ ν, EvLE g (s ν) := by
    intro g
    obtain ⟨ν, N, hν⟩ := hD g
    exact ⟨ν, (EvLE.trans ⟨N, hν⟩ (hsD ν))⟩
  obtain ⟨f, hf⟩ := exists_goodB_family d hd'
  have hmad := goodB_MAD hd' hdom hf
  exact ⟨members f, hmad, MADFamily_cardinal hmad,
    goodB_almostStronglySeparable hd' hdom hs_dom hs_mono
      (fun α n => le_max_right _ _) hf⟩

end Roitman.RecetaB
