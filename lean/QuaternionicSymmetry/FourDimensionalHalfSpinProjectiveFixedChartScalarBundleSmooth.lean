import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTarget

/-! The literal indexed local projective almost-complex map is jointly C∞
on point and tangent direction in scalar fixed-chart coordinates. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartScalarBundleSmooth

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveFixedChartTarget
  FourDimensionalHalfSpinProjectiveFirstTensorSmooth
  FourDimensionalHalfSpinProjectiveSecondTensorSmooth
  FourDimensionalHalfSpinProjectiveAllCoreTensorOverlap
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

private abbrev Model := ℍ × ℂ

def fixedScalarBundleMap (i : Fin 2) (p : M)
    (r : Model × Model) : Model × Model :=
  (r.1, indexedLocalTensor Q D i p r.1.1 r.1.2 r.2)

theorem fixedScalarBundleMap_smooth (i : Fin 2) (p : M) :
    ContDiffOn ℝ ∞ (fixedScalarBundleMap Q D i p)
      (((extChartAt 𝓘(ℝ, ℍ) p).target ×ˢ Set.univ) ×ˢ Set.univ) := by
  have hpoint : ContDiffOn ℝ ∞
      (fun r : Model × Model => r.1)
      (((extChartAt 𝓘(ℝ, ℍ) p).target ×ˢ Set.univ) ×ˢ Set.univ) :=
    contDiffOn_fst
  fin_cases i
  · exact hpoint.prodMk (by
      simpa only [fixedScalarBundleMap, indexedLocalTensor, ite_true] using
        first_local_tensor_apply_smooth Q D p)
  · exact hpoint.prodMk (by
      simpa only [fixedScalarBundleMap, indexedLocalTensor,
        show (1 : Fin 2) ≠ 0 by decide, ite_false] using
        second_local_tensor_apply_smooth Q D p)

theorem fixedScalarBundleMap_smoothAt (i : Fin 2) (p : M)
    (r : Model × Model)
    (hr : r.1.1 ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) :
    ContDiffAt ℝ ∞ (fixedScalarBundleMap Q D i p) r := by
  have hopen : IsOpen
      (((extChartAt 𝓘(ℝ, ℍ) p).target ×ˢ Set.univ) ×ˢ Set.univ : Set (Model × Model)) :=
    ((isOpen_extChartAt_target (I := 𝓘(ℝ, ℍ)) (x := p)).prod isOpen_univ).prod isOpen_univ
  exact (fixedScalarBundleMap_smooth Q D i p).contDiffAt
    (hopen.mem_nhds ⟨⟨hr, Set.mem_univ _⟩, Set.mem_univ _⟩)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartScalarBundleSmooth
