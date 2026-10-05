import QuaternionicSymmetry.ProjectorPeirceChartDerivative
import QuaternionicSymmetry.CompactSymplecticProjectorStrongChartMetricJet
import QuaternionicSymmetry.CompactSymplecticQuaternionicOrbit

/-! The Peirce projection fixes every genuine first derivative of the
actual projector immersion in a strong quotient chart. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongChartPeirceFixed

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbit
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ProjectorPeirceTangentProjection
open ProjectorPeirceChartDerivative
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem actual_chartDerivative_peirce_fixed
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
    ∀ (p : ProjectiveCarrier n) (y : EModel q)
      (hy : y ∈ (extChartAt 𝓘(ℝ,EModel q) p).target)
      (v : EModel q),
      let F := quotientOrbitProjector n ∘
        (extChartAt 𝓘(ℝ,EModel q) p).symm
      tangentPart (F y) (fderiv ℝ F y v) = fderiv ℝ F y v := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro p y hy v
  let F := quotientOrbitProjector n ∘
    (extChartAt 𝓘(ℝ,EModel q) p).symm
  have hσ : ContMDiffAt 𝓘(ℝ,EModel q) 𝓘(ℝ,EModel q) ∞
      (extChartAt 𝓘(ℝ,EModel q) p).symm y :=
    (contMDiffOn_extChartAt_symm (n := ∞) p y hy).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hy)
  have hF : DifferentiableAt ℝ F y :=
    ((smooth_quotientOrbitProjector_strongGauge
      hLee hDesc hImm n d e q g a hq hn).contMDiffAt.comp y hσ).contDiffAt
      |>.differentiableAt (by simp)
  have hid : ∀ z, F z * F z = F z := by
    intro z
    change quotientOrbitProjector n ((extChartAt 𝓘(ℝ,EModel q) p).symm z) *
      quotientOrbitProjector n ((extChartAt 𝓘(ℝ,EModel q) p).symm z) =
      quotientOrbitProjector n ((extChartAt 𝓘(ℝ,EModel q) p).symm z)
    induction ((extChartAt 𝓘(ℝ,EModel q) p).symm z) using Quotient.inductionOn' with
    | _ a => exact orbitProjector_idempotent n a
  exact chart_derivative_peirce_fixed n F y v hF hid

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongChartPeirceFixed
