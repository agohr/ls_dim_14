import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthVerticalMFDeriv

/-! The actual north projective-to-sphere manifold differential is
anti-complex for the quaternionic cross-product vertical tensor. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthVerticalSign

open scoped Manifold
open FourDimensionalHalfSpinProjectiveNorthVerticalMFDeriv
  FourDimensionalHalfSpinProjectiveNorthMFDeriv
  FourDimensionalHalfSpinProjectiveNorthDerivative
  FourDimensionalHalfSpinProjectiveNorthChartDerivative
  FourDimensionalHalfSpinHopfNorthDerivative
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinHopfProjectiveSmooth
  FourDimensionalTwistorHomogeneousFiber
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorVerticalComplex
  ManifoldTwistorSphereBundle

noncomputable section

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

private theorem north_vertical_coeff (v : Fin 1 → ℂ) :
    ((sphereTangentVerticalEquiv north)
      (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) projectiveHopfGeometric
        (affineSpinorPoint 0) v)).1 = northDifferential (v 0) := by
  change (EuclideanSpace.equiv (Fin 3) ℝ)
    (sphereTangentMap (coefficientSphereHomeomorph north)
      (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) projectiveHopfGeometric
        (affineSpinorPoint 0) v)) = northDifferential (v 0)
  have h := congrArg (fun L : (Fin 1 → ℂ) →L[ℝ] EuclideanThree =>
    (EuclideanSpace.equiv (Fin 3) ℝ) (L v)) north_hopf_sphere_mfderiv
  change (EuclideanSpace.equiv (Fin 3) ℝ)
      (sphereTangentMap (coefficientSphereHomeomorph north)
        (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) projectiveHopfGeometric
          (affineSpinorPoint 0) v)) =
    (EuclideanSpace.equiv (Fin 3) ℝ) (northEuclideanDifferential v) at h
  calc
    _ = (EuclideanSpace.equiv (Fin 3) ℝ)
          (northEuclideanDifferential v) := h
    _ = northDifferential (v 0) := by
      change (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ))
        (WithLp.toLp 2 (northDifferential (v 0))) = northDifferential (v 0)
      rfl

theorem north_projectiveHopf_mfderiv_anti_complex (v : Fin 1 → ℂ) :
    mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) projectiveHopfGeometric
      (affineSpinorPoint 0) (Complex.I • v) =
      -sphereVerticalComplex north
        (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) projectiveHopfGeometric
          (affineSpinorPoint 0) v) := by
  apply (sphereTangentVerticalEquiv north).injective
  rw [map_neg]
  have hc (w : TangentSpace (𝓡 2) (coefficientSphereHomeomorph north)) :
      sphereTangentVerticalEquiv north (sphereVerticalComplex north w) =
        verticalComplex north (sphereTangentVerticalEquiv north w) := by
    simp [sphereVerticalComplex]
  rw [hc]
  apply Subtype.ext
  change ((sphereTangentVerticalEquiv north)
    (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) projectiveHopfGeometric
      (affineSpinorPoint 0) (Complex.I • v))).1 =
    -crossProduct north.1
      ((sphereTangentVerticalEquiv north)
        (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) projectiveHopfGeometric
          (affineSpinorPoint 0) v)).1
  rw [north_vertical_coeff, north_vertical_coeff]
  change northDifferential ((Complex.I • v) 0) =
    -crossProduct north.1 (northDifferential (v 0))
  simpa only [Pi.smul_apply, smul_eq_mul] using
    northDifferential_anti_complex (v 0)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthVerticalSign
