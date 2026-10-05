import QuaternionicSymmetry.CompactSymplecticProjectorStrongLeviCivitaCurvature
import QuaternionicSymmetry.ProjectorPeirceCurvatureBracket
import QuaternionicSymmetry.ProjectorPeirceChartDerivative
import QuaternionicSymmetry.CompactSymplecticQuaternionicOrbit

/-! The actual ordinary Levi-Civita curvature of the projector quotient,
viewed by the genuine projector immersion, is the matrix double commutator.
This specializes the checked Peirce derivative formula; no model curvature
identity is assumed. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongCurvatureBracket

open Matrix Manifold Bundle GeneralLeviCivitaSource
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbit
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorStrongLeviCivitaCurvature
open CompactSymplecticProjectorStrongPeirceField
open ProjectorPeirceChartDerivative
open ProjectorPeirceCurvatureBracket
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem actual_leviCivita_curvature_eq_double_commutator
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
      (p : ProjectiveCarrier n) (y : EModel q)
      (hy : y ∈ (extChartAt 𝓘(ℝ,EModel q) p).target)
      (u v w : EModel q),
      let F := quotientOrbitProjector n ∘
        (extChartAt 𝓘(ℝ,EModel q) p).symm
      let X := fderiv ℝ F y u
      let Y := fderiv ℝ F y v
      let Z := fderiv ℝ F y w
      (fderiv ℝ F y)
        (LocalConnection.curvature (D.form p) y u v w) =
          commutator (commutator X Y) Z := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro D p y hy u v w
  letI : NormedSpace ℝ (Mat n) := inferInstance
  letI : NormedSpace ℝ (Mat n →L[ℝ] Mat n) := inferInstance
  letI : NormedAlgebra ℝ (EModel q →L[ℝ] EModel q) := inferInstance
  let F := quotientOrbitProjector n ∘ (extChartAt 𝓘(ℝ,EModel q) p).symm
  let proj := fun z => ProjectorPeirceContinuousProjection.tangentPartCLM n (F z)
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
  have hX := chart_derivative_peirce_tangent n F y u hF hid
  have hY := chart_derivative_peirce_tangent n F y v hF hid
  have hZ := chart_derivative_peirce_tangent n F y w hF hid
  have hcurv := actual_leviCivita_curvature_eq_peirce_derivative_commutator
    hLee hDesc hImm n d e q g a hq hn D p y hy u v w
  have hdu (A : Mat n) :
      (fderiv ℝ proj y u) A = tangentPartDerivative (F y) (fderiv ℝ F y u) A :=
    actual_peirceField_derivative_apply
      hLee hDesc hImm n d e q g a hq hn p y hy u A
  have hdv (A : Mat n) :
      (fderiv ℝ proj y v) A = tangentPartDerivative (F y) (fderiv ℝ F y v) A :=
    actual_peirceField_derivative_apply
      hLee hDesc hImm n d e q g a hq hn p y hy v A
  change (fderiv ℝ F y)
    (LocalConnection.curvature (D.form p) y u v w) = _
  rw [hcurv, hdu, hdv, hdu, hdv]
  exact derivative_commutator_eq_double_commutator
    (F y) (fderiv ℝ F y u) (fderiv ℝ F y v) (fderiv ℝ F y w)
    (hid y) hX hY hZ

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongCurvatureBracket
