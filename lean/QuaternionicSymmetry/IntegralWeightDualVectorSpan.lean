import QuaternionicSymmetry.TorusFaithfulWeightSpan
import QuaternionicSymmetry.IntegralWeightRealSpanComplexSeparation
import Mathlib.LinearAlgebra.Dual.Basis

/-! The real integral-weight functional and its literal coordinate vector
have equivalent spanning conditions. This matches the geometric dual-span
output to the character-separation input without an additional premise. -/
namespace QuaternionicSymmetry.IntegralWeightDualVectorSpan

open TorusFaithfulWeightSpan IntegralWeightRealSpanComplexSeparation
noncomputable section

def weightDualCoordinates (r : ℕ) :
    Module.Dual ℝ (Fin r → ℝ) ≃ₗ[ℝ] (Fin r → ℝ) :=
  (Pi.basisFun ℝ (Fin r)).dualBasis.equivFun

theorem weightDualCoordinates_integral {r : ℕ} (μ : Fin r → ℤ) :
    weightDualCoordinates r (integralWeightLinear μ) = realWeightVector μ := by
  funext j
  simp [weightDualCoordinates, Module.Basis.dualBasis_equivFun,
    integralWeightLinear_apply, Pi.basisFun_apply, realWeightVector,
    Pi.single_apply, mul_ite]

theorem real_vector_span_top_of_dual_span {r : ℕ} {ι : Type*}
    (μ : ι → Fin r → ℤ)
    (hSpan : Submodule.span ℝ
      (Set.range (fun i => integralWeightLinear (μ i))) = ⊤) :
    Submodule.span ℝ
      (Set.range (fun i => realWeightVector (μ i))) = ⊤ := by
  have h := congrArg (Submodule.map (weightDualCoordinates r).toLinearMap) hSpan
  rw [Submodule.map_span, Submodule.map_top] at h
  simpa only [← Set.range_comp, Function.comp_def,
    LinearEquiv.coe_coe, weightDualCoordinates_integral, LinearEquiv.range] using h

end
end QuaternionicSymmetry.IntegralWeightDualVectorSpan
