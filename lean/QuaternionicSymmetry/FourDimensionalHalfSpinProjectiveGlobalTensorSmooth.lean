import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTangentLeftInverse
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartGlobalTensorConjugacy

/-! The pointwise projective almost-complex operator is genuinely smooth
on the tangent bundle of the independent projective-spinor manifold atlas.
The proof uses arbitrary fixed affine charts and their actual tangent maps. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGlobalTensorSmooth

open scoped Quaternion Manifold ContDiff Topology
open FourDimensionalHalfSpinProjectiveFixedChartTangentCoordinates
  FourDimensionalHalfSpinProjectiveFixedChartTangentInverse
  FourDimensionalHalfSpinProjectiveFixedChartTangentLeftInverse
  FourDimensionalHalfSpinProjectiveFixedChartGlobalTensorConjugacy
  FourDimensionalHalfSpinProjectiveFixedChartScalarBundleSmooth
  FourDimensionalHalfSpinProjectiveFixedChartTarget
  FourDimensionalHalfSpinProjectiveFixedChartGerm
  FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS
  FourDimensionalHalfSpinProjectivePreferredChart
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveCore
  FourDimensionalHalfSpinProjective
  ComplexProjectiveTopology
  ManifoldQuaternionicReduction

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev productModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)
private abbrev ScalarModel := ℍ × ℂ

def tangentComplexBundleMap
    (t : TangentBundle productModel (SpinorBundleTotal Q)) :
    TangentBundle productModel (SpinorBundleTotal Q) :=
  ⟨t.1, tangentComplex Q D t.1 t.2⟩

theorem tangentComplexBundleMap_smooth :
    ContMDiff productModel.tangent productModel.tangent ∞
      (tangentComplexBundleMap Q D) := by
  intro t
  let p := t.1.1
  let i := preferredProjectiveChartIndex t.1.2
  let U : Set (TangentBundle productModel (SpinorBundleTotal Q)) :=
    (fun v => v.1) ⁻¹' fixedChartSource Q p i
  have ht : t ∈ U := by
    change t.1 ∈ fixedChartSource Q p i
    apply mem_fixedChartSource Q p i t.1 (mem_extChartAt_source t.1.1)
    rw [preferred_localTriv Q t.1]
    exact preferredProjectiveChartIndex_mem t.1.2
  have hOpen : IsOpen U :=
    (fixedChartSource_isOpen Q p i).preimage
      (FiberBundle.continuous_proj (ℍ × (Fin 1 → ℂ))
        (TangentSpace productModel (M := SpinorBundleTotal Q)))
  have hC := fixedTangentCoordinates_smoothOn Q p i
  have hMapC : Set.MapsTo (fixedTangentCoordinates Q p i) U
      {r | r.1 ∈ fixedChartTarget Q p i} := by
    intro v hv
    change (fixedTangentCoordinates Q p i v).1 ∈ fixedChartTarget Q p i
    rw [fixedTangentCoordinates_apply]
    exact fixedChart_mem_target Q p i v.1 hv
  have hJ : ContMDiffOn productModel.tangent
      (𝓘(ℝ, ScalarModel).prod 𝓘(ℝ, ScalarModel)) ∞
      (fixedScalarBundleMap Q D i p ∘ fixedTangentCoordinates Q p i) U := by
    have hLocal : ContMDiffOn
        (𝓘(ℝ, ScalarModel).prod 𝓘(ℝ, ScalarModel))
        (𝓘(ℝ, ScalarModel).prod 𝓘(ℝ, ScalarModel)) ∞
        (fixedScalarBundleMap Q D i p)
        {r | r.1 ∈ fixedChartTarget Q p i} := by
      intro r hr
      have hb := fixedChartTarget_base Q p i r.1 hr
      have hs := (fixedScalarBundleMap_smoothAt Q D i p r hb).contMDiffAt
      simpa only [chartedSpaceSelf_prod] using hs.contMDiffWithinAt
    exact hLocal.comp hC hMapC
  have hMapJ : Set.MapsTo
      (fixedScalarBundleMap Q D i p ∘ fixedTangentCoordinates Q p i)
      U {r | r.1 ∈ fixedChartTarget Q p i} := by
    intro v hv
    exact hMapC hv
  have hFinal : ContMDiffOn productModel.tangent productModel.tangent ∞
      (fixedTangentCoordinatesInv Q p i ∘
        (fixedScalarBundleMap Q D i p ∘ fixedTangentCoordinates Q p i)) U :=
    (fixedTangentCoordinatesInv_smoothOn Q p i).comp hJ hMapJ
  have hEq : ∀ v ∈ U, tangentComplexBundleMap Q D v =
      fixedTangentCoordinatesInv Q p i
        (fixedScalarBundleMap Q D i p (fixedTangentCoordinates Q p i v)) := by
    intro v hv
    have hp : v.1.1 ∈ (extChartAt 𝓘(ℝ, ℍ) p).source := by
      have hp' := ((projectiveSpinorCore Q).mem_localTriv_source (achart ℍ p) v.1).mp hv.1
      rw [← (projectiveSpinorCore Q).baseSet_at] at hp'
      simpa only [projectiveSpinorCore,
        ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
        tangentBundleCore_baseSet, coe_achart,
        ← extChartAt_source 𝓘(ℝ, ℍ)] using hp'
    have hc := tangentComplex_fixedChart_conjugacy Q D p i v.1 hp hv.2 v.2
    have hi := fixedTangentCoordinatesInv_left Q p i v.1 hv
      (tangentComplex Q D v.1 v.2)
    exact hi.symm.trans (congrArg (fixedTangentCoordinatesInv Q p i) (by
      simpa only [fixedTangentCoordinates_apply, fixedScalarBundleMap,
        tangentComplexBundleMap] using congrArg
          (fun x : ScalarModel => ((fixedProjectiveChart Q p i v.1), x)) hc))
  have hOn : ContMDiffOn productModel.tangent productModel.tangent ∞
      (tangentComplexBundleMap Q D) U :=
    hFinal.congr (fun v hv => by simpa only [Function.comp_apply] using hEq v hv)
  exact hOn.contMDiffAt (hOpen.mem_nhds ht)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGlobalTensorSmooth
