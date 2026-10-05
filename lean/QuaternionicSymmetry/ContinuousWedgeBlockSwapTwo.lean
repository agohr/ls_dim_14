import QuaternionicSymmetry.ContinuousWedge
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Group.Nat.Even

/-! The even permutation that moves a two-slot block past a block of any
length.  It is the index reordering behind cyclic trace of a two-form wedge
with a higher even form. -/

namespace QuaternionicSymmetry.ContinuousWedgeBlockSwapTwo

open Equiv

/-- Move the first two slots of `Fin (2+q)` behind the following `q` slots.
On indices this is addition by `q` modulo `2+q`. -/
def blockSwapTwo (q : ℕ) : Perm (Fin (2 + q)) :=
  finCycle ⟨q, by omega⟩

theorem blockSwapTwo_left (q : ℕ) (i : Fin 2) :
    blockSwapTwo q (Fin.castAdd q i) =
      (⟨q + i.val, by omega⟩ : Fin (2 + q)) := by
  apply Fin.ext
  simp only [blockSwapTwo, finCycle_apply, Fin.add_def,
    Fin.val_castAdd, Fin.val_mk]
  have hi : i.val < 2 := i.isLt
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem blockSwapTwo_right (q : ℕ) (j : Fin q) :
    blockSwapTwo q (Fin.natAdd 2 j) =
      (⟨j.val, by omega⟩ : Fin (2 + q)) := by
  apply Fin.ext
  simp only [blockSwapTwo, finCycle_apply, Fin.add_def,
    Fin.val_natAdd, Fin.val_mk]
  have hj : j.val < q := j.isLt
  have hsum : 2 + j.val + q = (2 + q) + j.val := by omega
  have hjlt : j.val < 2 + q := by omega
  rw [hsum, Nat.add_mod, Nat.mod_self, zero_add,
    Nat.mod_eq_of_lt hjlt]
  exact Nat.mod_eq_of_lt hjlt

theorem blockSwapTwo_eq_rotate_pow (q : ℕ) :
    blockSwapTwo q = (finRotate (2 + q)) ^ q := by
  ext i
  simp only [blockSwapTwo, finCycle_eq_finRotate_iterate]
  rfl

/-- Crossing two alternating slots over `q` slots has sign
`(-1)^(2q) = 1`, including the degenerate case `q=0`. -/
theorem blockSwapTwo_sign (q : ℕ) :
    Equiv.Perm.sign (blockSwapTwo q) = 1 := by
  rw [blockSwapTwo_eq_rotate_pow]
  simp only [map_pow]
  have hsize : 2 + q = (q + 1) + 1 := by omega
  rw [hsize, sign_finRotate]
  rw [← pow_mul]
  have heven : Even ((q + 1) * q) := by
    simpa [mul_comm] using Nat.even_mul_succ_self q
  exact heven.neg_one_pow

end QuaternionicSymmetry.ContinuousWedgeBlockSwapTwo
