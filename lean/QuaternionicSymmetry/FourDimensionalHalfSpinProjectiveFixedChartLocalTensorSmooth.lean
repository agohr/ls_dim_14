import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartGlobalTensorConjugacy
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualModelTensorSmooth

/-! The two local projective almost-complex operators, assembled by their
literal affine chart index, are smooth as maps on the actual independent
projective manifold's real tangent coordinate model. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartLocalTensorSmooth

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveActualModelTensorSmooth
  FourDimensionalHalfSpinProjectiveAllCoreTensorOverlap
  FourDimensionalHalfSpinProjectiveScalarFiber
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinProjectiveSecondTensor
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

private abbrev Model := ℍ × (Fin 1 → ℂ)

def indexedModelTensor (i : Fin 2) (p : M)
    (r : Model × Model) : Model :=
  projectiveTangentModelEquiv.symm
    (indexedLocalTensor Q D i p r.1.1 (r.1.2 0)
      (projectiveTangentModelEquiv r.2))

theorem indexedModelTensor_smooth (i : Fin 2) (p : M) :
    ContDiffOn ℝ ∞ (indexedModelTensor Q D i p)
      (((extChartAt 𝓘(ℝ, ℍ) p).target ×ˢ Set.univ) ×ˢ Set.univ) := by
  fin_cases i
  · simpa only [indexedModelTensor, indexedLocalTensor, ite_true,
      firstModelTensor] using first_model_tensor_smooth Q D p
  · simpa only [indexedModelTensor, indexedLocalTensor,
      show (1 : Fin 2) ≠ 0 by decide, ite_false,
      secondModelTensor] using second_model_tensor_smooth Q D p

def indexedModelBundleMap (i : Fin 2) (p : M)
    (r : Model × Model) : Model × Model :=
  (r.1, indexedModelTensor Q D i p r)

theorem indexedModelBundleMap_smooth (i : Fin 2) (p : M) :
    ContDiffOn ℝ ∞ (indexedModelBundleMap Q D i p)
      (((extChartAt 𝓘(ℝ, ℍ) p).target ×ˢ Set.univ) ×ˢ Set.univ) := by
  exact contDiffOn_fst.prodMk (indexedModelTensor_smooth Q D i p)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartLocalTensorSmooth
