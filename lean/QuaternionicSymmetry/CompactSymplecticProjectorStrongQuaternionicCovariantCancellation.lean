import QuaternionicSymmetry.CompactSymplecticProjectorStrongReflectedQuaternionicField
import QuaternionicSymmetry.GeneralLeviCivitaReflectionEndomorphismCancellation

/-! On the actual projector model, each smooth local quaternionic generator
and its genuine reflected field have cancelling ordinary Levi-Civita
covariant first jets at the reflection center. To conclude Q parallelism,
the reflected field must still be shown to lie in the local Q-plane. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicCovariantCancellation

open Filter Manifold Bundle GeneralLeviCivitaSource
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongQuaternionicPointIsometry
open CompactSymplecticProjectorStrongReflectedQuaternionicField
open CompactSymplecticProjectorStrongLeviCivitaSymmetryJet
open CompactSymplecticProjectorPointSymmetry
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicConnectionIsometrySolder
open ManifoldQuaternionicIsometryChartFields
open ManifoldQuaternionicLocalGeneratorField
open GeneralSmoothReflectedEndomorphismField
open GeneralLeviCivitaReflectionEndomorphismCancellation
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem actual_localGenerator_reflected_covariant_jets_cancel
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    ∀ (D : CoordinateLeviCivitaConnection
        (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn))
      (x : ProjectiveCarrier n) (t : Fin 3) (u v : EModel q),
      let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
      let f := pointSymmetryQuaternionicIsometry hLee hDesc hImm n d e q g a hq hn x
      let F := localIsometryChartMap Q f x
      let A := localChartGeneratorField Q.toSmoothAlmostQuaternionicTangent x t
      let B := reflectedField F A
      let y₀ := extChartAt 𝓘(ℝ,EModel q) x x
      covariantEndomorphismJet (D.form x y₀) A y₀ u v +
        covariantEndomorphismJet (D.form x y₀) B y₀ u v = 0 := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro D x t u v
  have hqpos : 0 < q := by omega
  letI : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
  letI : Nontrivial (EModel q) := inferInstance
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let f := pointSymmetryQuaternionicIsometry hLee hDesc hImm n d e q g a hq hn x
  let F := localIsometryChartMap Q f x
  let A := localChartGeneratorField Q.toSmoothAlmostQuaternionicTangent x t
  let B := reflectedField F A
  let y₀ := extChartAt 𝓘(ℝ,EModel q) x x
  have hpacket := actual_reflectedGenerator_smooth_and_intertwines
    hLee hDesc hImm n d e q g a hq hn x t
  have hA : DifferentiableAt ℝ A y₀ :=
    (localChartGeneratorField_contDiffAt_center Q.toSmoothAlmostQuaternionicTangent
      x t).differentiableAt (by norm_num)
  have hfix : f • x = x := by
    change pointSymmetry n x x = x
    exact pointSymmetry_fixed n x
  have hcenter : F y₀ = y₀ := by
    change localIsometryChartMap Q f x (extChartAt 𝓘(ℝ,EModel q) x x) = y₀
    rw [ManifoldQuaternionicIsometryTotalHorizontal.localIsometryChartMap_center Q f x,
      hfix]
  have hF : ContDiffAt ℝ 2 F y₀ := localIsometryChartMap_contDiffAt_center Q f x
  have hneg (z : EModel q) : fderiv ℝ F y₀ z = -z :=
    actual_pointSymmetry_chart_derivative_neg hLee hDesc hImm n d e q g a hq hn x z
  have hsecond (r s : EModel q) :
      fderiv ℝ (fderiv ℝ F) y₀ r s =
        -(D.form x y₀ r s + D.form x y₀ r s) :=
    actual_pointSymmetry_second_jet_eq_christoffel
      hLee hDesc hImm n d e q g a hq hn D x r s
  have heq : ∀ᶠ z in 𝓝 y₀,
      B (F z) ((fderiv ℝ F z) v) = (fderiv ℝ F z) (A z v) :=
    hpacket.2.2.mono (fun z hz => hz v)
  exact reflected_covariantEndomorphismJet_neg F A B (D.form x y₀)
    y₀ u v hF hA (by simpa only [hcenter] using hpacket.1)
    heq hcenter hneg hsecond hpacket.2.1

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicCovariantCancellation
