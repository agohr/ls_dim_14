import QuaternionicSymmetry.ContinuousAlgebraWedgePowers

/-! Complex scalar homogeneity of wedge powers of complex-algebra valued
forms on a real vector space. -/
namespace QuaternionicSymmetry.ComplexAlgebraWedgePowers
open ContinuousWedge ContinuousAlgebraWedgePowers
noncomputable section
variable {E R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R] [NormedAlgebra ℂ R]
  [IsScalarTower ℝ ℂ R]
local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

theorem wedge_smul {p q : ℕ} (c d : ℂ)
    (α : E [⋀^Fin p]→L[ℝ] R) (β : E [⋀^Fin q]→L[ℝ] R) :
    wedge (ContinuousLinearMap.mul ℝ R) (c • α) (d • β) =
      (c * d) • wedge (ContinuousLinearMap.mul ℝ R) α β := by
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [wedge_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousLinearMap.mul_apply', smul_mul_smul_comm]
  rw [smul_comm (c * d)]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact smul_comm (Equiv.Perm.sign σ) (c * d) _

theorem power_smul (c : ℂ) (α : E [⋀^Fin 2]→L[ℝ] R) (k : ℕ) :
    power (c • α) k = (c ^ (k + 1)) • power α k := by
  induction k with
  | zero => simp [power]
  | succ k ih =>
      change wedge (ContinuousLinearMap.mul ℝ R) (c • α) (power (c • α) k) = _
      rw [ih, wedge_smul]
      simp only [power, pow_succ']

end
end QuaternionicSymmetry.ComplexAlgebraWedgePowers
