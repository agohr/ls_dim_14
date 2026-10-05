import QuaternionicSymmetry.QuaternionicFundamentalDegree
import QuaternionicSymmetry.QuaternionicAction

/-! A basis-independent normalized top form built from the quaternionic
fundamental form. Nonvanishing is a separate exterior-algebra obligation. -/

namespace QuaternionicSymmetry.QuaternionicFundamental

open Module

noncomputable section

variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def topForm (Q : QuaternionicStructure V) (b : Basis ι ℝ V) : E V :=
  (((2 * Q.quaternionicDimension + 1).factorial : ℝ)⁻¹) •
    form Q b ^ Q.quaternionicDimension

theorem topForm_basis_independent {κ : Type*} [Fintype κ]
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V) (c : Basis κ ℝ V) :
    topForm Q b = topForm Q c := by
  unfold topForm
  rw [form_basis_independent Q b c]

theorem fundamental_pow_eq (Q : QuaternionicStructure V) (b : Basis ι ℝ V) :
    form Q b ^ Q.quaternionicDimension =
      ((2 * Q.quaternionicDimension + 1).factorial : ℝ) • topForm Q b := by
  rw [topForm, smul_smul, mul_inv_cancel₀ (by positivity :
    ((2 * Q.quaternionicDimension + 1).factorial : ℝ) ≠ 0), one_smul]

theorem topForm_mem_degree (Q : QuaternionicStructure V) (b : Basis ι ℝ V) :
    ((topForm Q b : E V) : ExteriorAlgebra ℝ (Module.Dual ℝ V)) ∈
      ExteriorAlgebra.exteriorPower ℝ (Module.finrank ℝ V) (Module.Dual ℝ V) := by
  rw [Q.real_finrank]
  exact (ExteriorAlgebra.exteriorPower ℝ (4 * Q.quaternionicDimension)
    (Module.Dual ℝ V)).smul_mem _ (form_pow_mem_degree Q b _)

theorem topForm_nonneg_iff (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (L : E V →ₗ[ℝ] ℝ) :
    0 ≤ L (topForm Q b) ↔ 0 ≤ L (form Q b ^ Q.quaternionicDimension) := by
  rw [fundamental_pow_eq Q b, map_smul, smul_eq_mul]
  exact (mul_nonneg_iff_of_pos_left (by positivity :
    (0 : ℝ) < (2 * Q.quaternionicDimension + 1).factorial)).symm

end
end QuaternionicSymmetry.QuaternionicFundamental
