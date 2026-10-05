import QuaternionicSymmetry.FourDimensionalTwistorAntipodalTensor
import QuaternionicSymmetry.ManifoldTwistorVerticalTangent

/-! The actual round-sphere antipodal derivative is coefficient negation,
and reverses the quaternionic vertical complex tensor. This is a statement
about genuine manifold derivatives, not only the coefficient-plane model. -/

namespace QuaternionicSymmetry.ManifoldTwistorSphereAntipodalDerivative

open scoped Manifold ContDiff Matrix
open ManifoldTwistorSphereBundle ManifoldTwistorCoefficientSphere
open ManifoldTwistorVerticalComplex FourDimensionalTwistorAntipodalTensor
open FourDimensionalHalfSpinAntipodalVerticalSign
noncomputable section

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

def geometricAntipodal (a : geometricSphere) : geometricSphere := -a

theorem geometricAntipodal_coefficient (a : coefficientSphere) :
    geometricAntipodal (coefficientSphereHomeomorph a) =
      coefficientSphereHomeomorph (antipodalCoefficient a) := by
  apply Subtype.ext
  rfl

theorem geometricAntipodal_smooth :
    ContMDiff (𝓡 2) (𝓡 2) ∞ geometricAntipodal :=
  contMDiff_neg_sphere

theorem sphereTangentMap_antipodal (a : geometricSphere)
    (v : TangentSpace (𝓡 2) a) :
    sphereTangentMap (geometricAntipodal a)
      (mfderiv (𝓡 2) (𝓡 2) geometricAntipodal a v) =
      -sphereTangentMap a v := by
  let R : EuclideanThree →L[ℝ] EuclideanThree := -ContinuousLinearMap.id ℝ _
  let ι : geometricSphere → EuclideanThree := Subtype.val
  have hfun : ι ∘ geometricAntipodal = R ∘ ι := rfl
  have hderiv := congrArg
    (fun F : geometricSphere → EuclideanThree =>
      mfderiv (𝓡 2) 𝓘(ℝ,EuclideanThree) F a v) hfun
  have hιa : MDifferentiableAt (𝓡 2) 𝓘(ℝ,EuclideanThree) ι
      (geometricAntipodal a) :=
    (contMDiff_coe_sphere (n := 2) (m := ∞)).mdifferentiableAt (by simp)
  have ha : MDifferentiableAt (𝓡 2) (𝓡 2) geometricAntipodal a :=
    geometricAntipodal_smooth.mdifferentiableAt (by simp)
  have hR : MDifferentiableAt 𝓘(ℝ,EuclideanThree) 𝓘(ℝ,EuclideanThree)
      R (ι a) := (R.contMDiff (n := ∞)).mdifferentiableAt (by simp)
  have hι : MDifferentiableAt (𝓡 2) 𝓘(ℝ,EuclideanThree) ι a :=
    (contMDiff_coe_sphere (n := 2) (m := ∞)).mdifferentiableAt (by simp)
  change mfderiv (𝓡 2) 𝓘(ℝ,EuclideanThree) (ι ∘ geometricAntipodal) a v =
    mfderiv (𝓡 2) 𝓘(ℝ,EuclideanThree) (R ∘ ι) a v at hderiv
  rw [mfderiv_comp a hιa ha, mfderiv_comp a hR hι] at hderiv
  change sphereTangentMap (geometricAntipodal a)
      (mfderiv (𝓡 2) (𝓡 2) geometricAntipodal a v) =
    (mfderiv 𝓘(ℝ,EuclideanThree) 𝓘(ℝ,EuclideanThree) R (ι a))
      (sphereTangentMap a v) at hderiv
  simpa only [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv,
    R, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply] using hderiv

theorem tangentVerticalEquiv_antipodal (a : coefficientSphere)
    (v : TangentSpace (𝓡 2) (coefficientSphereHomeomorph a)) :
    sphereTangentVerticalEquiv (antipodalCoefficient a)
      (mfderiv (𝓡 2) (𝓡 2) geometricAntipodal
        (coefficientSphereHomeomorph a) v) =
      verticalAntipodal a (sphereTangentVerticalEquiv a v) := by
  apply Subtype.ext
  change (EuclideanSpace.equiv (Fin 3) ℝ)
      (sphereTangentMap (geometricAntipodal (coefficientSphereHomeomorph a))
        (mfderiv (𝓡 2) (𝓡 2) geometricAntipodal
          (coefficientSphereHomeomorph a) v)) =
    -(EuclideanSpace.equiv (Fin 3) ℝ)
      (sphereTangentMap (coefficientSphereHomeomorph a) v)
  rw [sphereTangentMap_antipodal, map_neg]

theorem verticalAntipodal_anti_complex (a : coefficientSphere)
    (v : verticalSubmodule a) :
    verticalAntipodal a (verticalComplex a v) =
      -verticalComplex (antipodalCoefficient a) (verticalAntipodal a v) := by
  apply Subtype.ext
  change -(a.1 ⨯₃ v.1) = -((-a.1) ⨯₃ (-v.1))
  simp only [map_neg, neg_neg]
  rfl

theorem geometricAntipodal_anti_complex (a : coefficientSphere)
    (v : TangentSpace (𝓡 2) (coefficientSphereHomeomorph a)) :
    mfderiv (𝓡 2) (𝓡 2) geometricAntipodal (coefficientSphereHomeomorph a)
        (sphereVerticalComplex a v) =
      -sphereVerticalComplex (antipodalCoefficient a)
        (mfderiv (𝓡 2) (𝓡 2) geometricAntipodal
          (coefficientSphereHomeomorph a) v) := by
  apply (sphereTangentVerticalEquiv (antipodalCoefficient a)).injective
  rw [tangentVerticalEquiv_antipodal]
  simp only [sphereVerticalComplex, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply, map_neg]
  rw [tangentVerticalEquiv_antipodal]
  exact verticalAntipodal_anti_complex a _

end
end QuaternionicSymmetry.ManifoldTwistorSphereAntipodalDerivative
