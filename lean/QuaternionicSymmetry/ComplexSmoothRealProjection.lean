import QuaternionicSymmetry.ComplexSmoothRealDerivativeField
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! A complex-linear projection from bounded real-linear operators to
bounded complex-linear operators. -/

namespace QuaternionicSymmetry.ComplexSmoothRealProjection

open ComplexSmoothRealDerivativeField
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

private def realProjection (L : E →L[ℝ] F) : E →L[ℝ] F :=
  (1 / 2 : ℝ) •
    (L - Complex.I • (L.comp (Complex.I • (1 : E →L[ℝ] E))))

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
private theorem realProjection_commutes_i (L : E →L[ℝ] F) (v : E) :
    realProjection L (Complex.I • v) =
      Complex.I • realProjection L v := by
  simp [realProjection, smul_smul, Complex.I_mul_I, map_neg]
  simp only [smul_sub]
  rw [smul_comm Complex.I (2⁻¹ : ℝ) (L v),
    smul_comm Complex.I (2⁻¹ : ℝ) (Complex.I • L (Complex.I • v))]
  simp [smul_smul, Complex.I_mul_I]
  abel

/-- The complex-linear part of an arbitrary bounded real-linear map. -/
def complexProjectionValue (L : E →L[ℝ] F) : E →L[ℂ] F :=
  complexifyCommutingMap (realProjection L) (realProjection_commutes_i L)

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
theorem complexProjectionValue_of_complex
    (L : E →L[ℂ] F) :
    complexProjectionValue (L.restrictScalars ℝ) = L := by
  apply ContinuousLinearMap.ext
  intro v
  change realProjection (L.restrictScalars ℝ) v = L v
  simp [realProjection, Complex.I_mul_I, smul_smul, map_smul]
  module

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
private theorem complexProjectionValue_add (L K : E →L[ℝ] F) :
    complexProjectionValue (L + K) =
      complexProjectionValue L + complexProjectionValue K := by
  ext v
  change realProjection (L + K) v = realProjection L v + realProjection K v
  simp [realProjection, smul_add]
  module

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
private theorem complexProjectionValue_smul (c : ℂ) (L : E →L[ℝ] F) :
    complexProjectionValue (c • L) = c • complexProjectionValue L := by
  ext v
  change realProjection (c • L) v = c • realProjection L v
  simp [realProjection, smul_smul]
  module

/-- Continuous complex-linear projection onto the subspace of complex-linear
operators, with the real-linear operator space carrying output-wise complex
scalar multiplication. -/
def complexProjection : (E →L[ℝ] F) →L[ℂ] (E →L[ℂ] F) := by
  letI : FiniteDimensional ℂ (E →L[ℝ] F) :=
    Module.Finite.of_restrictScalars_finite ℝ ℂ (E →L[ℝ] F)
  let P : (E →L[ℝ] F) →ₗ[ℂ] (E →L[ℂ] F) :=
    { toFun := complexProjectionValue
      map_add' := complexProjectionValue_add
      map_smul' := complexProjectionValue_smul }
  exact ⟨P, P.continuous_of_finiteDimensional⟩

end
end QuaternionicSymmetry.ComplexSmoothRealProjection
