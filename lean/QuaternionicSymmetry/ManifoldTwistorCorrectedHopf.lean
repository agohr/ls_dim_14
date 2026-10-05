import QuaternionicSymmetry.ManifoldTwistorSphereAntipodalDerivative
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAllFiberVerticalSign
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfDiffeomorphPackage

/-! The antipodally corrected actual Hopf diffeomorphism intertwines the
standard CP¹ complex tangent with the genuine twistor-fiber complex tensor
at every point. It is the correctly signed fiber map, before inclusion in
an arbitrary twistor total space. -/

namespace QuaternionicSymmetry.ManifoldTwistorCorrectedHopf

open scoped Manifold ContDiff
open ManifoldTwistorSphereBundle ManifoldTwistorCoefficientSphere
open ManifoldTwistorVerticalComplex ManifoldTwistorSphereAntipodalDerivative
open FourDimensionalHalfSpinProjective FourDimensionalHalfSpinHopfProjectiveDescent
open FourDimensionalHalfSpinHopfProjectiveSmooth
open FourDimensionalHalfSpinProjectiveAllFiberVerticalSign
open FourDimensionalHalfSpinAntipodalVerticalSign
open FourDimensionalHalfSpinHopfDiffeomorphPackage
noncomputable section

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

def correctedHopf (p : ProjectiveSpinor) : geometricSphere :=
  geometricAntipodal (projectiveHopfGeometric p)

theorem correctedHopf_coefficient (p : ProjectiveSpinor) :
    correctedHopf p = coefficientSphereHomeomorph
      (antipodalCoefficient (projectiveHopf p)) :=
  geometricAntipodal_coefficient _

theorem correctedHopf_smooth :
    ContMDiff 𝓘(ℝ,Fin 1 → ℂ) (𝓡 2) ∞ correctedHopf :=
  geometricAntipodal_smooth.comp projectiveHopfGeometric_contMDiff

theorem correctedHopf_mfderiv (p : ProjectiveSpinor) (v : Fin 1 → ℂ) :
    mfderiv 𝓘(ℝ,Fin 1 → ℂ) (𝓡 2) correctedHopf p v =
      mfderiv (𝓡 2) (𝓡 2) geometricAntipodal (projectiveHopfGeometric p)
        (mfderiv 𝓘(ℝ,Fin 1 → ℂ) (𝓡 2) projectiveHopfGeometric p v) := by
  have h := mfderiv_comp p
    (geometricAntipodal_smooth.mdifferentiableAt (by simp))
    (projectiveHopfGeometric_contMDiff.mdifferentiableAt (by simp))
  exact congrArg (fun f => f v) h

theorem correctedHopf_mfderiv_complex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E] (S : QuaternionicStructure E)
    (p : ProjectiveSpinor) (v : Fin 1 → ℂ) :
    mfderiv 𝓘(ℝ,Fin 1 → ℂ) (𝓡 2) correctedHopf p (Complex.I • v) =
      sphereVerticalComplex (antipodalCoefficient (projectiveHopf p))
        (mfderiv 𝓘(ℝ,Fin 1 → ℂ) (𝓡 2) correctedHopf p v) := by
  rw [correctedHopf_mfderiv, correctedHopf_mfderiv]
  rw [projectiveHopf_mfderiv_anti_complex S, map_neg]
  change -(mfderiv (𝓡 2) (𝓡 2) geometricAntipodal
      (coefficientSphereHomeomorph (projectiveHopf p))
      (sphereVerticalComplex (projectiveHopf p)
        (mfderiv 𝓘(ℝ,Fin 1 → ℂ) (𝓡 2) projectiveHopfGeometric p v))) = _
  rw [geometricAntipodal_anti_complex, neg_neg]
  rfl

def sphereAntipodalDiffeomorph :
    Diffeomorph (𝓡 2) (𝓡 2) geometricSphere geometricSphere ∞ where
  toFun := geometricAntipodal
  invFun := geometricAntipodal
  left_inv a := by exact neg_neg a
  right_inv a := by exact neg_neg a
  contMDiff_toFun := geometricAntipodal_smooth
  contMDiff_invFun := geometricAntipodal_smooth

def correctedHopfDiffeomorph :
    Diffeomorph 𝓘(ℝ,Fin 1 → ℂ) (𝓡 2) ProjectiveSpinor geometricSphere ∞ :=
  projectiveHopfGeometricDiffeomorph.trans sphereAntipodalDiffeomorph

@[simp] theorem correctedHopfDiffeomorph_apply (p : ProjectiveSpinor) :
    correctedHopfDiffeomorph p = correctedHopf p := rfl

end
end QuaternionicSymmetry.ManifoldTwistorCorrectedHopf
