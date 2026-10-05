import QuaternionicSymmetry.QuaternionicNormalizerVerticalCovariance

/-! The coefficient-plane covariance is now compared with the genuine
manifold derivative on the independently smooth geometric sphere. -/

namespace QuaternionicSymmetry.QuaternionicNormalizerSphereTangentCovariance

open scoped Manifold
open QuaternionicIsometryNormalizer
  FourDimensionalTwistorNormalizerQuotient
  ManifoldTwistorSphereBundle
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorVerticalComplex
  QuaternionicNormalizerSphereSmooth
  QuaternionicNormalizerVerticalCovariance

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  (S : QuaternionicStructure E)

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

private theorem tangentVerticalEquiv_complex
    (a : coefficientSphere)
    (v : TangentSpace (𝓡 2) (coefficientSphereHomeomorph a)) :
    sphereTangentVerticalEquiv a (sphereVerticalComplex a v) =
      verticalComplex a (sphereTangentVerticalEquiv a v) := by
  simp [sphereVerticalComplex]

theorem tangentVerticalEquiv_geometricAction
    (g : normalizer S) (a : ManifoldTwistorSphereBundle.coefficientSphere)
    (v : TangentSpace (𝓡 2) (coefficientSphereHomeomorph a)) :
    sphereTangentVerticalEquiv (act S g a)
      (mfderiv (𝓡 2) (𝓡 2) (geometricAction S g)
        (coefficientSphereHomeomorph a) v) =
      verticalRotation S g a (sphereTangentVerticalEquiv a v) := by
  apply Subtype.ext
  change (EuclideanSpace.equiv (Fin 3) ℝ)
      (sphereTangentMap (geometricAction S g
        (coefficientSphereHomeomorph a))
        (mfderiv (𝓡 2) (𝓡 2) (geometricAction S g)
          (coefficientSphereHomeomorph a) v)) =
      rotationLinear S g ((EuclideanSpace.equiv (Fin 3) ℝ)
        (sphereTangentMap (coefficientSphereHomeomorph a) v))
  rw [sphereTangentMap_geometricAction S g]
  rfl

theorem sphereVerticalComplex_geometricAction
    (g : normalizer S) (a : ManifoldTwistorSphereBundle.coefficientSphere)
    (v : TangentSpace (𝓡 2) (coefficientSphereHomeomorph a)) :
    mfderiv (𝓡 2) (𝓡 2) (geometricAction S g)
      (coefficientSphereHomeomorph a) (sphereVerticalComplex a v) =
      sphereVerticalComplex (act S g a)
        (mfderiv (𝓡 2) (𝓡 2) (geometricAction S g)
          (coefficientSphereHomeomorph a) v) := by
  apply (sphereTangentVerticalEquiv (act S g a)).injective
  rw [tangentVerticalEquiv_geometricAction S g a,
    tangentVerticalEquiv_complex a,
    tangentVerticalEquiv_complex (act S g a),
    tangentVerticalEquiv_geometricAction S g a]
  change verticalRotation S g a (verticalComplex a
      (sphereTangentVerticalEquiv a v)) =
    verticalComplex (act S g a)
      (verticalRotation S g a (sphereTangentVerticalEquiv a v))
  exact verticalRotation_complex S g a _

end
end QuaternionicSymmetry.QuaternionicNormalizerSphereTangentCovariance
