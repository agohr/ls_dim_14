import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartAsAtlas

/-! The true source of a fixed affine chart equals the source of the
independent projective-bundle chart centered at its coordinate pole. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartAtlasSource

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveFixedChartAsAtlas
  FourDimensionalHalfSpinProjectiveFixedChartPole
  FourDimensionalHalfSpinProjectiveFixedChartGerm
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveCore
  FourDimensionalHalfSpinProjectivePreferredChart
  FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS
  ManifoldQuaternionicReduction
  ComplexProjectiveTopology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

private abbrev productModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)

theorem fixedChartSource_eq_poleAtlas_source (p : M) (i : Fin 2) :
    fixedChartSource Q p i =
      (extChartAt productModel (chartPole Q p i)).source := by
  let Z := projectiveSpinorCore Q
  let L := (Z.localTriv (achart ℍ p)).toOpenPartialHomeomorph
  have htriv : chartAt (M × FourDimensionalHalfSpinProjective.ProjectiveSpinor)
      (chartPole Q p i) = L := rfl
  have hval : L (chartPole Q p i) = (p, coordinatePole i) := by
    apply Prod.ext
    · rfl
    · exact preferred_localTriv Q (chartPole Q p i)
  ext z
  simp only [extChartAt_source, chartAt_comp,
    prodChartedSpace_chartAt,
    OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.prod_source]
  rw [htriv, hval]
  simp only [Prod.fst, Prod.snd, selected_projective_chart,
    preferredIndex_coordinatePole, projectiveChart_source,
    Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod]
  constructor
  · intro hz
    refine ⟨hz.1, ?_, hz.2⟩
    have hp' := (Z.mem_localTriv_source (achart ℍ p) z).mp hz.1
    rw [← Z.baseSet_at] at hp'
    have hp : z.1 ∈ (extChartAt 𝓘(ℝ, ℍ) p).source := by
      simpa only [Z, projectiveSpinorCore,
        ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
        tangentBundleCore_baseSet, coe_achart,
        ← extChartAt_source 𝓘(ℝ, ℍ)] using hp'
    have hproj : (L z).1 = z.1 := by
      change ((Z.localTriv (achart ℍ p)) z).1 = z.1
      rw [Z.localTriv_apply]
    rw [hproj]
    simpa only [extChartAt_source] using hp
  · intro hz
    exact ⟨hz.1, hz.2.2⟩

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartAtlasSource
