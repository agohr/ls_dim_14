import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAffineHolomorphic

/-! The actual indexed corrected Hopf fiber derivative commutes with
complex rotation in its first affine coordinate at every point.  The
proof uses the holomorphicity of literal projectivization, not a chosen
projective atlas selector. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfIndexedVerticalComplex

open scoped Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative
  FourDimensionalHalfSpinProjectiveAffineHolomorphic
  ManifoldTwistorCorrectedHopf
  ManifoldTwistorVerticalComplex
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinAntipodalVerticalSign

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  (S : QuaternionicStructure E)

theorem indexedCorrectedHopf_zero_mfderiv_complex
    (S : QuaternionicStructure E) (z w : ℂ) :
    mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 0) z
      (Complex.I • w) =
      sphereVerticalComplex (antipodalCoefficient
        (projectiveHopf (affineSpinorPoint z)))
        (mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 0) z w) := by
  have hproj : MDifferentiableAt 𝓘(ℝ,ℂ)
      𝓘(ℝ, Fin 1 → ℂ) affineSpinorPoint z :=
    (ManifoldComplexHolomorphicFactorization.holomorphic_is_real_smooth
      affineSpinorPoint_holomorphic).mdifferentiableAt (by simp)
  have hhopf : MDifferentiableAt 𝓘(ℝ,Fin 1 → ℂ) (𝓡 2)
      correctedHopf (affineSpinorPoint z) :=
    correctedHopf_smooth.mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp z hhopf hproj
  change mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 0) z =
    (mfderiv 𝓘(ℝ,Fin 1 → ℂ) (𝓡 2) correctedHopf
      (affineSpinorPoint z)).comp
      (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 1 → ℂ) affineSpinorPoint z) at hcomp
  rw [hcomp]
  change mfderiv 𝓘(ℝ,Fin 1 → ℂ) (𝓡 2) correctedHopf
      (affineSpinorPoint z)
      (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 1 → ℂ)
        affineSpinorPoint z (Complex.I • w)) =
    sphereVerticalComplex (antipodalCoefficient
      (projectiveHopf (affineSpinorPoint z)))
      (mfderiv 𝓘(ℝ,Fin 1 → ℂ) (𝓡 2) correctedHopf
        (affineSpinorPoint z)
        (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 1 → ℂ) affineSpinorPoint z w))
  rw [affineSpinorPoint_real_mfderiv_complex]
  exact correctedHopf_mfderiv_complex S _ _

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfIndexedVerticalComplex
