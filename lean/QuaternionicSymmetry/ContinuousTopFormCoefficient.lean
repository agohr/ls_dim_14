import QuaternionicSymmetry.ContinuousWedge
import QuaternionicSymmetry.PositiveRay
import Mathlib.LinearAlgebra.Determinant

/-! Intrinsic scalar comparison against a nonzero continuous top form.
The coefficient is independent of the basis used to compute it. -/
namespace QuaternionicSymmetry.ContinuousTopFormCoefficient

open Module
noncomputable section
variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]

def evaluationLinear (v : ι → V) : (V [⋀^ι]→L[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun α := α v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def evaluation (v : ι → V) : (V [⋀^ι]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  (evaluationLinear v).mkContinuous (∏ i, ‖v i‖) fun α => by
    simpa [evaluationLinear, mul_comm] using α.le_opNorm v

@[simp] theorem evaluation_apply (v : ι → V) (α : V [⋀^ι]→L[ℝ] ℝ) :
    evaluation v α = α v := rfl

def coefficient (b : Basis ι ℝ V) (ν : V [⋀^ι]→L[ℝ] ℝ) :
    (V [⋀^ι]→L[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun α := α b / ν b
  map_add' α β := by simp [add_div]
  map_smul' r α := by simp [mul_div_assoc]

omit [Fintype ι] in
@[simp] theorem coefficient_apply (b : Basis ι ℝ V) (ν α : V [⋀^ι]→L[ℝ] ℝ) :
    coefficient b ν α = α b / ν b := rfl

theorem eval_basis_ne_zero (b : Basis ι ℝ V) (ν : V [⋀^ι]→L[ℝ] ℝ) (hν : ν ≠ 0) :
    ν b ≠ 0 := by
  apply (ν.toAlternatingMap.map_basis_ne_zero_iff b).mpr
  intro h
  apply hν
  ext v
  exact congrArg (fun f : V [⋀^ι]→ₗ[ℝ] ℝ => f v) h

theorem eq_coefficient_smul (b : Basis ι ℝ V) (ν α : V [⋀^ι]→L[ℝ] ℝ)
    (hν : ν ≠ 0) : α = coefficient b ν α • ν := by
  classical
  have ha := α.toAlternatingMap.eq_smul_basis_det b
  have hv := ν.toAlternatingMap.eq_smul_basis_det b
  ext v
  have ha' := congrArg (fun f : V [⋀^ι]→ₗ[ℝ] ℝ => f v) ha
  have hv' := congrArg (fun f : V [⋀^ι]→ₗ[ℝ] ℝ => f v) hv
  change α v = α b * b.det v at ha'
  change ν v = ν b * b.det v at hv'
  change α v = (α b / ν b) * ν v
  rw [ha', hv']
  field_simp [eval_basis_ne_zero b ν hν]

/-- Evaluation of a pulled-back top form has the exact determinant factor. -/
theorem eval_comp_basis (b : Basis ι ℝ V) (α : V [⋀^ι]→L[ℝ] ℝ) (L : V →L[ℝ] V) :
    (α.compContinuousLinearMap L) b = L.toLinearMap.det * α b := by
  classical
  have h := α.toAlternatingMap.eq_smul_basis_det b
  have hv := congrArg (fun f : V [⋀^ι]→ₗ[ℝ] ℝ => f (fun i => L (b i))) h
  change α (fun i => L (b i)) = α b * b.det (fun i => L (b i)) at hv
  change α (fun i => L (b i)) = _
  rw [hv]
  have hd := b.det_comp L.toLinearMap b
  simp only [Basis.det_self, mul_one] at hd
  rw [show b.det (fun i => L (b i)) = L.toLinearMap.det from hd]
  ring

theorem coefficient_self (b : Basis ι ℝ V) (ν : V [⋀^ι]→L[ℝ] ℝ) (hν : ν ≠ 0) :
    coefficient b ν ν = 1 := div_self (eval_basis_ne_zero b ν hν)

theorem coefficient_eq_iff (b : Basis ι ℝ V) (ν α : V [⋀^ι]→L[ℝ] ℝ)
    (hν : ν ≠ 0) (r : ℝ) : coefficient b ν α = r ↔ α = r • ν := by
  constructor
  · intro h
    simpa only [h] using eq_coefficient_smul b ν α hν
  · rintro rfl
    rw [map_smul, coefficient_self b ν hν, smul_eq_mul, mul_one]

theorem coefficient_basis_independent (b c : Basis ι ℝ V)
    (ν α : V [⋀^ι]→L[ℝ] ℝ) (hν : ν ≠ 0) :
    coefficient b ν α = coefficient c ν α := by
  apply (coefficient_eq_iff b ν α hν _).mpr
  exact eq_coefficient_smul c ν α hν

theorem contains_iff_coefficient_nonneg (b : Basis ι ℝ V)
    (ν α : V [⋀^ι]→L[ℝ] ℝ) (hν : ν ≠ 0) :
    PositiveRay.Contains ν α ↔ 0 ≤ coefficient b ν α := by
  constructor
  · rintro ⟨r, hr, he⟩
    rwa [(coefficient_eq_iff b ν α hν r).mpr he]
  · intro h
    exact ⟨coefficient b ν α, h, eq_coefficient_smul b ν α hν⟩

end
end QuaternionicSymmetry.ContinuousTopFormCoefficient
