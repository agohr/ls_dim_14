import QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondAffineHolomorphic
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfIndexedVerticalComplex

/-! Complex-linearity of the corrected Hopf derivative in the literal
second affine CP¹ coordinate, including its origin. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondVerticalComplex

open scoped Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectivePreferredSecondPoint
  FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative
  FourDimensionalHalfSpinHopfSecondAffineHolomorphic
  ManifoldTwistorCorrectedHopf
  ManifoldTwistorVerticalComplex
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinAntipodalVerticalSign
  ManifoldComplexHolomorphicFactorization

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  (S : QuaternionicStructure E)

theorem indexedCorrectedHopf_one_mfderiv_complex
    (S : QuaternionicStructure E) (z w : ℂ) :
    mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 1) z
      (Complex.I • w) =
      sphereVerticalComplex (antipodalCoefficient
        (projectiveHopf (secondAffineSpinorPoint z)))
        (mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 1) z w) := by
  have hproj : MDifferentiableAt 𝓘(ℝ,ℂ)
      𝓘(ℝ, Fin 1 → ℂ) secondAffineSpinorPoint z :=
    (holomorphic_is_real_smooth
      secondAffineSpinorPoint_holomorphic).mdifferentiableAt (by simp)
  have hhopf : MDifferentiableAt 𝓘(ℝ,Fin 1 → ℂ) (𝓡 2)
      correctedHopf (secondAffineSpinorPoint z) :=
    correctedHopf_smooth.mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp z hhopf hproj
  change mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 1) z =
    (mfderiv 𝓘(ℝ,Fin 1 → ℂ) (𝓡 2) correctedHopf
      (secondAffineSpinorPoint z)).comp
      (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 1 → ℂ) secondAffineSpinorPoint z) at hcomp
  rw [hcomp]
  change mfderiv 𝓘(ℝ,Fin 1 → ℂ) (𝓡 2) correctedHopf
      (secondAffineSpinorPoint z)
      (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 1 → ℂ)
        secondAffineSpinorPoint z (Complex.I • w)) =
    sphereVerticalComplex (antipodalCoefficient
      (projectiveHopf (secondAffineSpinorPoint z)))
      (mfderiv 𝓘(ℝ,Fin 1 → ℂ) (𝓡 2) correctedHopf
        (secondAffineSpinorPoint z)
        (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 1 → ℂ)
          secondAffineSpinorPoint z w))
  rw [secondAffineSpinorPoint_real_mfderiv_complex]
  exact correctedHopf_mfderiv_complex S _ _

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondVerticalComplex
