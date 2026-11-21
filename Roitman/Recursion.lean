import Mathlib.Order.WellFounded
import Mathlib.Logic.Function.Basic

/-! A local extension principle for well-ordered recursion.
The extension hypothesis is explicit: this theorem alone is not the
construction lemma from the manuscript. -/
namespace Roitman

theorem local_recursion {ι X : Type*} [LinearOrder ι] [WellFoundedLT ι]
    [Inhabited X] (P : ι → (ι → X) → Prop)
    (locality : ∀ i f g, (∀ j, j ≤ i → f j = g j) → (P i f ↔ P i g))
    (extend : ∀ i f, (∀ j, j < i → P j f) →
      ∃ x, P i (Function.update f i x)) :
    ∃ f, ∀ i, P i f := by
  classical
  let chooseStep : ι → (ι → X) → X := fun i f =>
    if h : ∃ x, P i (Function.update f i x) then h.choose else default
  let step : (i : ι) → ((j : ι) → j < i → X) → X := fun i rec =>
    chooseStep i (fun j => if h : j < i then rec j h else default)
  let f : ι → X := WellFounded.fix wellFounded_lt step
  have fix_eq (i : ι) :
      f i = chooseStep i (fun j => if h : j < i then f j else default) := by
    exact WellFounded.fix_eq wellFounded_lt step i
  refine ⟨f, ?_⟩
  intro i
  induction i using (wellFounded_lt (α := ι)).induction with
  | h i ih =>
    let prev : ι → X := fun j => if j < i then f j else default
    have hp : ∀ j, j < i → P j prev := by
      intro j hj
      apply (locality j f prev ?_).mp (ih j hj)
      intro k hk
      simp only [prev, ite_eq_left (lt_of_le_of_lt hk hj)]
    have hex := extend i prev hp
    have chosen : P i (Function.update prev i (chooseStep i prev)) := by
      simpa only [chooseStep, dite_eq_left hex] using hex.choose_spec
    apply (locality i (Function.update prev i (chooseStep i prev)) f ?_).mp chosen
    intro j hj
    by_cases heq : j = i
    · subst j
      simpa only [Function.update_self, prev, dite_eq_ite] using (fix_eq i).symm
    · have hlt : j < i := lt_of_le_of_ne hj heq
      simp [Function.update_of_ne heq, prev, hlt]

end Roitman


