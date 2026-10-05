import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGlobalTensorSmooth

/-! The independent projective-spinor total space carries a genuine smooth
almost-complex tangent endomorphism: globally C∞, fiberwise real-linear,
and squaring to minus the identity. Integrability is not asserted. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGlobalAlmostComplex

open scoped Manifold ContDiff Quaternion
open FourDimensionalHalfSpinProjectiveGlobalTensorSmooth
  FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS
  FourDimensionalHalfSpinProjectiveManifold

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev projectiveModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)

theorem tangentComplexBundleMap_projection
    (t : TangentBundle projectiveModel (SpinorBundleTotal Q)) :
    (tangentComplexBundleMap Q D t).1 = t.1 := rfl

theorem tangentComplexBundleMap_sq
    (t : TangentBundle projectiveModel (SpinorBundleTotal Q)) :
    tangentComplexBundleMap Q D (tangentComplexBundleMap Q D t) =
      (⟨t.1,-t.2⟩ : TangentBundle projectiveModel (SpinorBundleTotal Q)) := by
  apply Bundle.TotalSpace.ext
  · rfl
  · apply heq_of_eq
    exact tangentComplex_sq Q D t.1 t.2

theorem tangentComplexBundleMap_contMDiff :
    ContMDiff projectiveModel.tangent projectiveModel.tangent ∞
      (tangentComplexBundleMap Q D) :=
  tangentComplexBundleMap_smooth Q D

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGlobalAlmostComplex
