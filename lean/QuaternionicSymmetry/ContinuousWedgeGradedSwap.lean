import QuaternionicSymmetry.ContinuousAlternationTransport
import QuaternionicSymmetry.ContinuousWedge
import QuaternionicSymmetry.LocalTraceSquareAlgebra
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Group.Nat.Even

/-! Block permutation and graded commutativity for scalar normalized wedges. -/

namespace QuaternionicSymmetry.ContinuousWedgeGradedSwap

open QuaternionicSymmetry.ContinuousAlternation
  QuaternionicSymmetry.ContinuousAlternationTransport
  QuaternionicSymmetry.ContinuousMultilinearProduct
  QuaternionicSymmetry.ContinuousWedge
  QuaternionicSymmetry.LocalTraceSquareAlgebra
  Equiv

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p q : ℕ}

/-- Move a nonempty left block of length p past a nonempty right block of
length q. -/
def blockSwap (p q : ℕ) (hp : 0 < p) :
    Equiv.Perm (Fin (p + q)) :=
  finCycle ⟨q, by omega⟩

theorem blockSwap_left (hp : 0 < p) (i : Fin p) :
    blockSwap p q hp (Fin.castAdd q i) =
      finCongr (Nat.add_comm q p) (Fin.natAdd q i) := by
  apply Fin.ext
  simp only [blockSwap, finCycle_apply, Fin.add_def,
    Fin.val_castAdd, Fin.val_natAdd, finCongr_apply_coe]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem blockSwap_right (hp : 0 < p) (j : Fin q) :
    blockSwap p q hp (Fin.natAdd p j) =
      finCongr (Nat.add_comm q p) (Fin.castAdd p j) := by
  apply Fin.ext
  simp only [blockSwap, finCycle_apply, Fin.add_def,
    Fin.val_natAdd, Fin.val_castAdd, finCongr_apply_coe]
  have hj : j.val < q := j.isLt
  have hjlt : j.val < p + q := by omega
  have hsum : p + j.val + q = (p + q) + j.val := by omega
  rw [hsum, Nat.add_mod, Nat.mod_self, zero_add,
    Nat.mod_eq_of_lt hjlt]
  exact Nat.mod_eq_of_lt hjlt

theorem blockSwap_sign (hp : 0 < p) (hq : 0 < q) :
    Equiv.Perm.sign (blockSwap p q hp) = (-1 : ℤˣ) ^ (p * q) := by
  have hrotate : blockSwap p q hp = (finRotate (p + q)) ^ q := by
    ext i
    simp only [blockSwap, finCycle_eq_finRotate_iterate]
    rfl
  rw [hrotate, map_pow]
  have hsize : p + q = (p + q - 1) + 1 := by omega
  rw [hsize, sign_finRotate]
  rw [← pow_mul]
  have hsplit : p + q - 1 = p + (q - 1) := by omega
  rw [hsplit, add_mul, pow_add]
  have heven : Even ((q - 1) * q) := by
    simpa only [Nat.sub_add_cancel hq] using Nat.even_mul_succ_self (q - 1)
  rw [heven.neg_one_pow, mul_one]

private def rawLeft
    (α : E [⋀^Fin p]→L[ℝ] ℝ)
    (β : E [⋀^Fin q]→L[ℝ] ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (p + q) => E) ℝ :=
  (concatenate (ContinuousLinearMap.mul ℝ ℝ)
    α.toContinuousMultilinearMap β.toContinuousMultilinearMap).domDomCongr
      (finSumFinEquiv (m := p) (n := q))

private def rawRight
    (β : E [⋀^Fin q]→L[ℝ] ℝ)
    (α : E [⋀^Fin p]→L[ℝ] ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (q + p) => E) ℝ :=
  (concatenate (ContinuousLinearMap.mul ℝ ℝ)
    β.toContinuousMultilinearMap α.toContinuousMultilinearMap).domDomCongr
      (finSumFinEquiv (m := q) (n := p))

private theorem raw_swap (hp : 0 < p)
    (α : E [⋀^Fin p]→L[ℝ] ℝ)
    (β : E [⋀^Fin q]→L[ℝ] ℝ) :
    (rawRight β α).domDomCongr (finCongr (Nat.add_comm q p)) =
      (rawLeft α β).domDomCongr (blockSwap p q hp) := by
  ext v
  simp only [rawLeft, rawRight,
    ContinuousMultilinearMap.domDomCongr_apply, concatenate_apply,
    Function.comp_def, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  have hα : (fun i : Fin p =>
      v (finCongr (Nat.add_comm q p) (Fin.natAdd q i))) =
      (fun i : Fin p => v (blockSwap p q hp (Fin.castAdd q i))) := by
    funext i
    rw [blockSwap_left hp i]
  have hβ : (fun j : Fin q =>
      v (finCongr (Nat.add_comm q p) (Fin.castAdd p j))) =
      (fun j : Fin q => v (blockSwap p q hp (Fin.natAdd p j))) := by
    funext j
    rw [blockSwap_right hp j]
  rw [hα, hβ]
  exact mul_comm _ _

/-- Scalar normalized wedges obey the Koszul sign under block exchange. -/
theorem wedge_swap (hp : 0 < p) (hq : 0 < q)
    (α : E [⋀^Fin p]→L[ℝ] ℝ)
    (β : E [⋀^Fin q]→L[ℝ] ℝ)
    (v : Fin (p + q) → E) :
    wedge (ContinuousLinearMap.mul ℝ ℝ) β α
        (v ∘ finCongr (Nat.add_comm q p)) =
      (-1 : ℝ) ^ (p * q) •
        wedge (ContinuousLinearMap.mul ℝ ℝ) α β v := by
  change (((q.factorial * p.factorial : ℕ) : ℝ)⁻¹ •
    alternationCLM (rawRight β α))
      (v ∘ finCongr (Nat.add_comm q p)) =
    (-1 : ℝ) ^ (p * q) •
      ((((p.factorial * q.factorial : ℕ) : ℝ)⁻¹) •
        alternationCLM (rawLeft α β)) v
  simp only [ContinuousAlternatingMap.smul_apply]
  rw [← alternationCLM_domDomCongr_apply
    (rawRight β α) (finCongr (Nat.add_comm q p)) v]
  rw [raw_swap hp α β, alternation_domDomCongr]
  rw [blockSwap_sign hp hq]
  simp [Units.smul_def, Nat.cast_mul,
    mul_comm, mul_left_comm, mul_assoc]

end
end QuaternionicSymmetry.ContinuousWedgeGradedSwap
