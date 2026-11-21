import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Countable

/-! Bookkeeping for the recursion: a small copy of omega one, enumerations
of its proper initial segments, and schedules repeating every requirement. -/

noncomputable section

namespace Roitman.Bookkeeping

open Set Ordinal Cardinal

/-- The countable ordinals, represented by a type in universe zero. -/
abbrev I := (ω₁ : Ordinal.{0}).ToType

instance : Nonempty I :=
  Ordinal.nonempty_toType_iff.mpr (Cardinal.isSuccLimit_omega 1).bot_lt.ne'

instance : OrderBot I := WellFoundedLT.toOrderBot I

theorem cardinal_I : Cardinal.mk I = ℵ₁ := by
  simp [I]

/-- Adding a finite sequence of natural numbers does not enlarge omega one. -/
def normalizedIndexEquiv : (I × List ℕ) ≃ I :=
  Classical.choice (Cardinal.eq.mp (by
    simp only [Cardinal.mk_prod, Cardinal.lift_id, cardinal_I,
      Cardinal.mk_list_eq_max_mk_aleph0, Cardinal.mk_nat, max_self]
    exact Cardinal.mul_eq_left Cardinal.aleph0_lt_aleph_one.le
      Cardinal.aleph0_lt_aleph_one.le Cardinal.aleph0_ne_zero))

instance countableIio (a : I) : Countable (Set.Iio a) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  apply Cardinal.lt_aleph_one_iff.mp
  have h := Cardinal.mk_Iio_lt a (by simp [I])
  simpa [cardinal_I] using h

instance countableIic (a : I) : Countable (Set.Iic a) := by
  have h : (Set.Iic a).Countable := by
    rw [← Set.Iio_insert]
    exact (Set.to_countable (Set.Iio a)).insert a
  exact h.to_subtype

/-- An enumeration of the earlier indices, permitting `none` at empty stages. -/
def enumEarlier (a : I) (n : ℕ) : Option I :=
  letI := Encodable.ofCountable (Set.Iio a)
  (Encodable.decode n : Option (Set.Iio a)).map Subtype.val

theorem enumEarlier_lt {a j : I} {n : ℕ}
    (h : enumEarlier a n = some j) : j < a := by
  unfold enumEarlier at h
  obtain ⟨k, _, hk⟩ := Option.map_eq_some_iff.mp h
  exact hk ▸ k.property

theorem enumEarlier_complete {a j : I} (h : j < a) :
    ∃ n, enumEarlier a n = some j := by
  letI := Encodable.ofCountable (Set.Iio a)
  refine ⟨Encodable.encode (⟨j, h⟩ : Set.Iio a), ?_⟩
  simp [enumEarlier, Encodable.encodek]

/-- A surjective enumeration of a nonempty countable requirement type. -/
def enumerate (R : Type*) [Countable R] [Nonempty R] : ℕ → R :=
  letI := Encodable.ofCountable R
  fun n => (Encodable.decode n).getD (Classical.choice ‹Nonempty R›)

theorem enumerate_surjective (R : Type*) [Countable R] [Nonempty R] :
    Function.Surjective (enumerate R) := by
  letI := Encodable.ofCountable R
  exact Encodable.surjective_decode_getD R _

/-- Every requirement appears infinitely often in this schedule. -/
def fairSchedule (R : Type*) [Countable R] [Nonempty R] (n : ℕ) : R :=
  enumerate R (Nat.unpair n).1

theorem fairSchedule_infinite (R : Type*) [Countable R] [Nonempty R] (r : R) :
    {n | fairSchedule R n = r}.Infinite := by
  obtain ⟨k, hk⟩ := enumerate_surjective R r
  apply (Set.infinite_range_of_injective (f := fun n => Nat.pair k n) ?_).mono
  · rintro _ ⟨n, rfl⟩
    simpa [fairSchedule] using hk
  · intro n m h
    exact (Nat.pair_eq_pair.mp h).2

/-- The ordinal represented by an index. -/
def ord (a : I) : Ordinal := a.toOrd.val

theorem ord_lt_omega_one (a : I) : ord a < ω₁ := a.toOrd.property

@[simp] theorem ord_le_ord {a b : I} : ord a ≤ ord b ↔ a ≤ b :=
  Ordinal.ToType.mk.symm.le_iff_le

@[simp] theorem ord_lt_ord {a b : I} : ord a < ord b ↔ a < b :=
  Ordinal.ToType.mk.symm.lt_iff_lt

private def raiseStep (f : I → I) (a : I) (previous : ∀ b, b < a → I) : I :=
  Ordinal.ToType.mk ⟨max (ord (f a))
      (⨆ b : Set.Iio a, Order.succ (ord (previous b.val b.property))), by
    apply max_lt (ord_lt_omega_one (f a))
    apply Ordinal.iSup_lt_omega_one
    intro b
    exact (Cardinal.isSuccLimit_omega 1).succ_lt (ord_lt_omega_one _)⟩

private theorem ord_raiseStep (f : I → I) (a : I) (previous : ∀ b, b < a → I) :
    ord (raiseStep f a previous) = max (ord (f a))
      (⨆ b : Set.Iio a, Order.succ (ord (previous b.val b.property))) := by
  simp [ord, raiseStep]

private theorem raiseStep_bound (f : I → I) (a : I) (previous : ∀ b, b < a → I) :
    f a ≤ raiseStep f a previous := by
  rw [← ord_le_ord, ord_raiseStep]
  exact le_max_left _ _

private theorem raiseStep_previous (f : I → I) (a b : I)
    (previous : ∀ b, b < a → I) (h : b < a) :
    previous b h < raiseStep f a previous := by
  rw [← ord_lt_ord, ord_raiseStep]
  apply (Order.lt_succ (ord (previous b h))).trans_le
  exact (Ordinal.le_iSup _ (⟨b, h⟩ : Set.Iio a)).trans (le_max_right _ _)

/-- Raise any map on omega one to a strictly increasing pointwise majorant. -/
private def raise (f : I → I) : I → I :=
  wellFounded_lt.fix (raiseStep f)

private theorem raise_eq (f : I → I) (a : I) :
    raise f a = raiseStep f a (fun b _ => raise f b) := by
  exact WellFounded.fix_eq _ _ _

private theorem le_raise (f : I → I) (a : I) : f a ≤ raise f a := by
  rw [raise_eq]
  exact raiseStep_bound _ _ _

private theorem raise_strictMono (f : I → I) : StrictMono (raise f) := by
  intro a b h
  rw [raise_eq f b]
  exact raiseStep_previous f b a _ h

private def pairEquiv : (I × I) ≃ I :=
  Classical.choice (Cardinal.eq.mp (by
    simp only [Cardinal.mk_prod, Cardinal.lift_id, cardinal_I]
    exact Cardinal.mul_eq_self Cardinal.aleph0_lt_aleph_one.le))

/-- An injective assignment of pair requirements to stages. Unassigned stages
are allowed; the assigned stage is always late enough to know its first index. -/
def gamma (p : I × I) : I :=
  raise (fun a => (pairEquiv.symm a).1) (pairEquiv p)

theorem gamma_injective : Function.Injective gamma :=
  (raise_strictMono _).injective.comp pairEquiv.injective

theorem le_gamma (a b : I) : a ≤ gamma (a, b) := by
  simpa [gamma] using le_raise (fun a => (pairEquiv.symm a).1) (pairEquiv (a, b))

/-- At unassigned stages we repeat the harmless requirement `(⊥, ⊥)`. -/
def task (i : I) : I × I := by
  classical
  exact if h : ∃ p, gamma p = i then h.choose else (⊥, ⊥)

theorem task_gamma (p : I × I) : task (gamma p) = p := by
  classical
  have h : ∃ q, gamma q = gamma p := ⟨p, rfl⟩
  simp only [task, dite_eq_left h]
  exact gamma_injective h.choose_spec

theorem task_fst_le (i : I) : (task i).1 ≤ i := by
  classical
  unfold task
  split_ifs with h
  · have hle := le_gamma h.choose.1 h.choose.2
    simpa only [Prod.mk.eta, h.choose_spec] using hle
  · exact bot_le

end Roitman.Bookkeeping
