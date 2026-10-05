import QuaternionicSymmetry.CompactSymplecticProjectorStrongCurvatureBracket
import QuaternionicSymmetry.CompactSymplecticProjectorStrongChartMetricPullback
import QuaternionicSymmetry.ProjectorFrobeniusCurvature

/-! The actual quotient metric has nonnegative sectional-curvature
numerator: the Levi-Civita curvature pairing is the squared Frobenius norm
of the commutator of the genuine projector derivatives. Strict positivity
requires the separate rank-one tangent commutator rigidity theorem. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongCurvatureNonnegative

open Matrix Manifold Bundle GeneralLeviCivitaSource
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbit
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorStrongChartMetricPullback
open CompactSymplecticProjectorStrongCurvatureBracket
open CompactSymplecticProjectorAmbientMetric
open ProjectorFrobeniusCurvature
open ProjectorPeirceCurvatureBracket
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

private def adjointCLM (n : ℕ) : Mat n →L[ℝ] Mat n :=
  (show Mat n →ₗ[ℝ] Mat n from {
    toFun := Matrix.conjTranspose
    map_add' := by intro A B; simp
    map_smul' := by intro c A; simp
  }).toContinuousLinearMap

private theorem fderiv_selfAdjoint (n q : ℕ) (F : EModel q → Mat n)
    (y u : EModel q) (hF : DifferentiableAt ℝ F y)
    (hself : ∀ z, (F z)ᴴ = F z) :
    (fderiv ℝ F y u)ᴴ = fderiv ℝ F y u := by
  have hfun : (fun A : Mat n => Aᴴ) ∘ F = F := funext hself
  have hcomp := fderiv_comp y (adjointCLM n).differentiableAt hF
  change fderiv ℝ ((fun A : Mat n => Aᴴ) ∘ F) y = _ at hcomp
  rw [hfun, (adjointCLM n).fderiv] at hcomp
  have hv := congrArg (fun L : EModel q →L[ℝ] Mat n => L u) hcomp
  simpa [adjointCLM] using hv.symm

theorem actual_leviCivita_curvature_pairing_eq_commutator_square
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
      (u v : EModel q),
      let F := quotientOrbitProjector n ∘
        (extChartAt 𝓘(ℝ,EModel q) p).symm
      let X := fderiv ℝ F y u
      let Y := fderiv ℝ F y v
      chartMetric
        (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn)
        p y (LocalConnection.curvature (D.form p) y u v v) u =
          frobeniusPairing n (commutator X Y) (commutator X Y) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro D p y hy u v
  letI : NormedSpace ℝ (Mat n) := inferInstance
  letI : NormedAlgebra ℝ (EModel q →L[ℝ] EModel q) := inferInstance
  let F := quotientOrbitProjector n ∘ (extChartAt 𝓘(ℝ,EModel q) p).symm
  have hσ : ContMDiffAt 𝓘(ℝ,EModel q) 𝓘(ℝ,EModel q) ∞
      (extChartAt 𝓘(ℝ,EModel q) p).symm y :=
    (contMDiffOn_extChartAt_symm (n := ∞) p y hy).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hy)
  have hF : DifferentiableAt ℝ F y :=
    ((smooth_quotientOrbitProjector_strongGauge
      hLee hDesc hImm n d e q g a hq hn).contMDiffAt.comp y hσ).contDiffAt
      |>.differentiableAt (by simp)
  have hself : ∀ z, (F z)ᴴ = F z := by
    intro z
    change (quotientOrbitProjector n
      ((extChartAt 𝓘(ℝ,EModel q) p).symm z))ᴴ =
        quotientOrbitProjector n ((extChartAt 𝓘(ℝ,EModel q) p).symm z)
    induction ((extChartAt 𝓘(ℝ,EModel q) p).symm z) using Quotient.inductionOn' with
    | _ a => exact orbitProjector_selfAdjoint n a
  have hY : (fderiv ℝ F y v)ᴴ = fderiv ℝ F y v :=
    fderiv_selfAdjoint n q F y v hF hself
  have hcurv := actual_leviCivita_curvature_eq_double_commutator
    hLee hDesc hImm n d e q g a hq hn D p y hy u v v
  have hmetric := actual_chartMetric_eq_frobenius_chart_derivatives
    hLee hDesc hImm n d e q g a hq hn p y hy
    (LocalConnection.curvature (D.form p) y u v v) u
  change _ = frobeniusPairing n (commutator (fderiv ℝ F y u)
    (fderiv ℝ F y v)) (commutator (fderiv ℝ F y u)
    (fderiv ℝ F y v))
  rw [hmetric, hcurv, frobeniusCLM_apply]
  exact frobenius_double_commutator_eq_commutator_square n _ _ hY

theorem actual_leviCivita_curvature_pairing_nonneg
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
      (u v : EModel q),
      0 ≤ chartMetric
        (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn)
        p y (LocalConnection.curvature (D.form p) y u v v) u := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro D p y hy u v
  rw [actual_leviCivita_curvature_pairing_eq_commutator_square
    hLee hDesc hImm n d e q g a hq hn D p y hy u v]
  exact frobeniusPairing_self_nonneg n _

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongCurvatureNonnegative
