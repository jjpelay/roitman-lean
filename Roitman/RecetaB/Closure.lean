import Roitman.Bookkeeping

/-!
# Closure points

Every map `F : ω₁ → ω₁` has a nonzero closure point `δ`, i.e. `F γ < δ` for
all `γ < δ`. Used in the almost strong separability argument of recipe B.
-/

noncomputable section
namespace Roitman.RecetaB
open Roitman Bookkeeping Ordinal

private def ofOrd (o : Ordinal.{0}) (h : o < ω₁) : I := Ordinal.ToType.mk ⟨o, h⟩

private theorem ord_ofOrd (o : Ordinal.{0}) (h : o < ω₁) : Bookkeeping.ord (ofOrd o h) = o := by
  simp [Bookkeeping.ord, ofOrd]

private def closeStep (F : I → I) (a : I) : I :=
  ofOrd (max (Order.succ (Bookkeeping.ord a)) (⨆ γ : Set.Iic a, Order.succ (Bookkeeping.ord (F γ.val)))) (by
    apply max_lt ((Cardinal.isSuccLimit_omega 1).succ_lt (Bookkeeping.ord_lt_omega_one a))
    apply Ordinal.iSup_lt_omega_one
    intro γ
    exact (Cardinal.isSuccLimit_omega 1).succ_lt (Bookkeeping.ord_lt_omega_one _))

private theorem lt_closeStep (F : I → I) (a : I) : a < closeStep F a := by
  rw [← Bookkeeping.ord_lt_ord, closeStep, ord_ofOrd]
  exact (Order.lt_succ (Bookkeeping.ord a)).trans_le (le_max_left _ _)

private theorem F_lt_closeStep (F : I → I) {a γ : I} (h : γ ≤ a) :
    F γ < closeStep F a := by
  rw [← Bookkeeping.ord_lt_ord, closeStep, ord_ofOrd]
  apply (Order.lt_succ (Bookkeeping.ord (F γ))).trans_le
  exact (Ordinal.le_iSup (fun γ : Set.Iic a => Order.succ (Bookkeeping.ord (F γ.val))) ⟨γ, h⟩).trans
    (le_max_right _ _)

theorem exists_closed (F : I → I) : ∃ δ : I, ⊥ < δ ∧ ∀ γ, γ < δ → F γ < δ := by
  let seq : ℕ → I := fun n => (closeStep F)^[n] ⊥
  have hsup : (⨆ n, ord (seq n)) < ω₁ :=
    Ordinal.iSup_lt_omega_one (fun n => Bookkeeping.ord_lt_omega_one _)
  refine ⟨ofOrd _ hsup, ?_, ?_⟩
  · rw [← Bookkeeping.ord_lt_ord, ord_ofOrd]
    apply lt_of_lt_of_le _ (Ordinal.le_iSup (fun n => ord (seq n)) 1)
    rw [Bookkeeping.ord_lt_ord]
    simpa [seq] using lt_closeStep F ⊥
  · intro γ hγ
    rw [← Bookkeeping.ord_lt_ord, ord_ofOrd] at hγ ⊢
    obtain ⟨n, hn⟩ := Ordinal.lt_iSup_iff.mp hγ
    rw [Bookkeeping.ord_lt_ord] at hn
    have h1 : F γ < seq (n + 1) := by
      simp only [seq, Function.iterate_succ_apply']
      exact F_lt_closeStep F hn.le
    exact (Bookkeeping.ord_lt_ord.mpr h1).trans_le (Ordinal.le_iSup (fun n => ord (seq n)) (n + 1))

end Roitman.RecetaB
