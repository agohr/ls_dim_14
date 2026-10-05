import QuaternionicSymmetry.CompactSymplecticProjectorStrongHessianConstraints
import QuaternionicSymmetry.CompactSymplecticProjectorStrongChartTangentRange
import QuaternionicSymmetry.CompactSymplecticProjectorPeirceQuaternionic

/-! The Peirce component of the actual projector Hessian lies in the
actual differential image in every strong quotient chart. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongHessianPeirceRange

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbit
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorStrongHessianConstraints
open CompactSymplecticProjectorStrongChartTangentRange
open CompactSymplecticProjectorPeirceQuaternionic
open ProjectorPeirceTangentProjection
open CompactSymplecticQuaternionicOrbit
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem actual_chartHessian_peircePart_in_derivative_range
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
      (u v : EModel q),
      let x := (extChartAt 𝓘(ℝ,EModel q) p).symm y
      let F := quotientOrbitProjector n ∘
        (extChartAt 𝓘(ℝ,EModel q) p).symm
      let H := fderiv ℝ (fderiv ℝ F) y u v
      ∃ w : EModel q,
        fderiv ℝ F y w = tangentPart (quotientOrbitProjector n x) H := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro p y hy u v
  let x := (extChartAt 𝓘(ℝ,EModel q) p).symm y
  let P : Mat n := quotientOrbitProjector n x
  let H : Mat n := fderiv ℝ
    (fderiv ℝ (quotientOrbitProjector n ∘
      (extChartAt 𝓘(ℝ,EModel q) p).symm)) y u v
  have hPself : Pᴴ = P := by
    change (quotientOrbitProjector n x)ᴴ = quotientOrbitProjector n x
    induction x using Quotient.inductionOn' with
    | _ z => exact orbitProjector_selfAdjoint n z
  have hPid : P * P = P := by
    change quotientOrbitProjector n x * quotientOrbitProjector n x =
      quotientOrbitProjector n x
    induction x using Quotient.inductionOn' with
    | _ z => exact orbitProjector_idempotent n z
  have hPquat : P * CompactSymplecticHaar.standardJ (n + 1) =
      CompactSymplecticHaar.standardJ (n + 1) * P.map star := by
    change quotientOrbitProjector n x * CompactSymplecticHaar.standardJ (n + 1) =
      CompactSymplecticHaar.standardJ (n + 1) * (quotientOrbitProjector n x).map star
    induction x using Quotient.inductionOn' with
    | _ z => exact orbitProjector_commutes_quaternionicJ n z
  exact actual_chartDerivative_covers_quaternionicHermitian_tangent
    hLee hDesc hImm n d e q g a hq hn p y hy (tangentPart P H)
    (tangentPart_hermitian n P H hPself
      (actual_chartHessian_selfAdjoint hLee hDesc hImm
        n d e q g a hq hn p y hy u v))
    (tangentPart_tangent P H hPid)
    (tangentPart_quaternionic n (CompactSymplecticHaar.standardJ (n + 1)) P H
      hPquat (actual_chartHessian_quaternionic hLee hDesc hImm
        n d e q g a hq hn p y hy u v))

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongHessianPeirceRange
