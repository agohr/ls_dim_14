import QuaternionicSymmetry.QuaternionicNormalizerSphereSmooth

/-! The actual normalizer coefficient rotation transports every vertical
quaternionic complex plane and intertwines its cross-product complex
structure. -/

namespace QuaternionicSymmetry.QuaternionicNormalizerVerticalCovariance

open QuaternionicIsometryNormalizer
  QuaternionicNormalizerRotationAxes
  QuaternionicNormalizerCrossCovariance
  FourDimensionalTwistorNormalizerQuotient
  ManifoldTwistorVerticalComplex
  ManifoldTwistorSphereBundle

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  (S : QuaternionicStructure E)

def verticalRotation (g : normalizer S) (a : coefficientSphere) :
    verticalSubmodule a →ₗ[ℝ] verticalSubmodule (act S g a) where
  toFun v := ⟨rotationLinear S g v.1, by
    have h := rotation_dot S g a.1 v.1
    change (rotationLinear S g a.1) ⬝ᵥ (rotationLinear S g v.1) = 0
    rw [show (rotationLinear S g a.1) ⬝ᵥ
      (rotationLinear S g v.1) = a.1 ⬝ᵥ v.1 from h]
    exact v.2⟩
  map_add' u v := by
    apply Subtype.ext
    exact (rotationLinear S g).map_add u.1 v.1
  map_smul' r v := by
    apply Subtype.ext
    exact (rotationLinear S g).map_smul r v.1

theorem verticalRotation_complex (g : normalizer S)
    (a : coefficientSphere) (v : verticalSubmodule a) :
    verticalRotation S g a (verticalComplex a v) =
      verticalComplex (act S g a) (verticalRotation S g a v) := by
  apply Subtype.ext
  exact rotation_cross S g a.1 v.1

end
end QuaternionicSymmetry.QuaternionicNormalizerVerticalCovariance
