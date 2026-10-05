import QuaternionicSymmetry.FourDimensionalHalfSpinAntipodalVerticalSign
import QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplex

/-! The coefficient antipodal map reverses both the base and vertical pieces
of the actual quaternionic twistor almost-complex tensor. This checks the
local tensor convention quoted by Hitchin, without asserting any new
identification with his projective negative-half-spin atlas. -/

namespace QuaternionicSymmetry.FourDimensionalTwistorAntipodalTensor

set_option maxHeartbeats 30000

open scoped Manifold Quaternion Matrix
open FourDimensionalHalfSpinAntipodalVerticalSign
  ManifoldTwistorVerticalComplex
  ManifoldTwistorLocalAlmostComplex
  ManifoldTwistorSphereBundle
  VectorBundleFrameTransitions.QuaternionicFrameReduction

noncomputable section

def verticalAntipodal (a : coefficientSphere) :
    verticalSubmodule a →ₗ[ℝ] verticalSubmodule (antipodalCoefficient a) where
  toFun v := ⟨-v.1, by
    have hv : a.1 ⬝ᵥ v.1 = 0 := v.2
    change (-a.1) ⬝ᵥ (-v.1) = 0
    simpa only [dotProduct, Pi.neg_apply, neg_mul_neg] using hv⟩
  map_add' v w := by
    apply Subtype.ext
    change -(v.1 + w.1) = -v.1 + -w.1
    abel
  map_smul' r v := by
    apply Subtype.ext
    simp

def rawAntipodal {E : Type*} [AddCommGroup E] [Module ℝ E]
    (a : coefficientSphere) :
    (E × verticalSubmodule a) →ₗ[ℝ]
      (E × verticalSubmodule (antipodalCoefficient a)) where
  toFun uv := (uv.1, verticalAntipodal a uv.2)
  map_add' v w := by
    apply Prod.ext
    · rfl
    · simp [map_add]
  map_smul' r v := by
    apply Prod.ext
    · rfl
    · simp [map_smul]

theorem rawAntipodal_splitComplex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] (S : QuaternionicStructure E)
    (a : coefficientSphere) (uv : E × verticalSubmodule a) :
    rawAntipodal a (splitComplex S a uv) =
      -splitComplex S (antipodalCoefficient a) (rawAntipodal a uv) := by
  apply Prod.ext
  · change baseComplex S a uv.1 =
        -(baseComplex S (antipodalCoefficient a) uv.1)
    change synth S a.1 uv.1 = -(synth S (-a.1) uv.1)
    have hneg : synth S (-a.1) uv.1 = -(synth S a.1 uv.1) := by
      rw [map_neg]
      rfl
    rw [hneg, neg_neg]
  · apply Subtype.ext
    change -(a.1 ⨯₃ uv.2.1) =
      -((-a.1) ⨯₃ (-uv.2.1))
    simp only [map_neg, neg_neg]
    rfl

end
end QuaternionicSymmetry.FourDimensionalTwistorAntipodalTensor
