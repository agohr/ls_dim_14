import QuaternionicSymmetry.CompactSymplecticProjectorStrongSymmetryChartDerivativeInverse
import QuaternionicSymmetry.ManifoldQuaternionicLocalGeneratorField
import QuaternionicSymmetry.GeneralSmoothReflectedEndomorphismField
import QuaternionicSymmetry.CompactSymplecticProjectorStrongLeviCivitaSymmetryJet

/-! Actual local quaternionic generator fields on the projector quotient,
reflected through an actual point symmetry. The reflected fields are
smooth at the center, agree with the original generators there, and obey
the genuine derivative intertwining law on a neighborhood. Their Q-plane
membership is a separate fixed-chart span-transport proof. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongReflectedQuaternionicField

open Filter Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongQuaternionicPointIsometry
open CompactSymplecticProjectorStrongSymmetryChartInvolution
open CompactSymplecticProjectorStrongSymmetryChartDerivativeInverse
open CompactSymplecticProjectorStrongLeviCivitaSymmetryJet
open CompactSymplecticProjectorPointSymmetry
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicConnectionIsometrySolder
open ManifoldQuaternionicIsometryChartFields
open ManifoldQuaternionicLocalGeneratorField
open GeneralSmoothReflectedEndomorphismField
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem actual_reflectedGenerator_smooth_and_intertwines
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) (t : Fin 3) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
    let f := pointSymmetryQuaternionicIsometry hLee hDesc hImm n d e q g a hq hn x
    let F := localIsometryChartMap Q f x
    let A := localChartGeneratorField Q.toSmoothAlmostQuaternionicTangent x t
    let B := reflectedField F A
    let y₀ := extChartAt 𝓘(ℝ,EModel q) x x
    DifferentiableAt ℝ B y₀ ∧ B y₀ = A y₀ ∧
      ∀ᶠ z in 𝓝 y₀, ∀ v : EModel q,
        B (F z) ((fderiv ℝ F z) v) = (fderiv ℝ F z) (A z v) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  have hqpos : 0 < q := by omega
  letI : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
  letI : Nontrivial (EModel q) := inferInstance
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let f := pointSymmetryQuaternionicIsometry hLee hDesc hImm n d e q g a hq hn x
  let F := localIsometryChartMap Q f x
  let A := localChartGeneratorField Q.toSmoothAlmostQuaternionicTangent x t
  let B := reflectedField F A
  let y₀ := extChartAt 𝓘(ℝ,EModel q) x x
  have hfix : f • x = x := by
    change pointSymmetry n x x = x
    exact pointSymmetry_fixed n x
  have hcenter : F y₀ = y₀ := by
    change localIsometryChartMap Q f x (extChartAt 𝓘(ℝ,EModel q) x x) = y₀
    rw [ManifoldQuaternionicIsometryTotalHorizontal.localIsometryChartMap_center Q f x,
      hfix]
  have hF : ContDiffAt ℝ 2 F y₀ :=
    localIsometryChartMap_contDiffAt_center Q f x
  have hA : DifferentiableAt ℝ A y₀ :=
    (localChartGeneratorField_contDiffAt_center Q.toSmoothAlmostQuaternionicTangent
      x t).differentiableAt (by norm_num)
  have hneg (v : EModel q) : fderiv ℝ F y₀ v = -v :=
    actual_pointSymmetry_chart_derivative_neg hLee hDesc hImm n d e q g a hq hn x v
  constructor
  · exact reflectedField_differentiableAt_center F A y₀ hF hcenter hA
  constructor
  · exact reflectedField_eq_self_center F A y₀ hcenter hneg
  · exact reflectedField_intertwines_eventually F A y₀
      (actual_pointSymmetry_chart_involutive_eventually
        hLee hDesc hImm n d e q g a hq hn x)
      (actual_pointSymmetry_chart_derivative_inverse_eventually
        hLee hDesc hImm n d e q g a hq hn x)

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongReflectedQuaternionicField
