import QuaternionicSymmetry.CompactSymplecticProjectorStrongHessianLinearConstraint
import QuaternionicSymmetry.CompactSymplecticQuaternionicOrbit

/-! The actual strong-chart projector Hessian is Hermitian and obeys
the quaternionic anti-linear commutation law. Both follow by twice
differentiating the genuine orbit equations. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongHessianConstraints

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbit
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open CompactSymplecticQuaternionicOrbit
open CompactSymplecticProjectorStrongHessianLinearConstraint
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

private def selfAdjointConstraint (n : ℕ) : Mat n →L[ℝ] Mat n :=
  adjointCLM n - ContinuousLinearMap.id ℝ (Mat n)

private def quaternionicConstraint (n : ℕ) : Mat n →L[ℝ] Mat n :=
  (show Mat n →ₗ[ℝ] Mat n from {
    toFun := fun A => A * CompactSymplecticHaar.standardJ (n + 1) -
      CompactSymplecticHaar.standardJ (n + 1) * A.map star
    map_add' := by
      intro A B
      simp [add_mul, mul_add, Matrix.map_add, sub_add_sub_comm]
    map_smul' := by
      intro c A
      simp [Matrix.map_smul, smul_sub]
  }).toContinuousLinearMap

theorem actual_chartHessian_selfAdjoint
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
      let F := quotientOrbitProjector n ∘
        (extChartAt 𝓘(ℝ,EModel q) p).symm
      (fderiv ℝ (fderiv ℝ F) y u v)ᴴ =
        fderiv ℝ (fderiv ℝ F) y u v := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro p y hy u v
  have hvalue : ∀ x : ProjectiveCarrier n,
      selfAdjointConstraint n (quotientOrbitProjector n x) = 0 := by
    intro x
    induction x using Quotient.inductionOn' with
    | _ z =>
      change (orbitProjector n z)ᴴ - orbitProjector n z = 0
      rw [orbitProjector_selfAdjoint]
      simp
  have hder := actual_chartHessian_linear_constraint hLee hDesc hImm
    n d e q g a hq hn (selfAdjointConstraint n) hvalue p y hy u v
  dsimp [selfAdjointConstraint, adjointCLM] at hder
  exact sub_eq_zero.mp hder

theorem actual_chartHessian_quaternionic
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
      let F := quotientOrbitProjector n ∘
        (extChartAt 𝓘(ℝ,EModel q) p).symm
      let H := fderiv ℝ (fderiv ℝ F) y u v
      H * CompactSymplecticHaar.standardJ (n + 1) =
        CompactSymplecticHaar.standardJ (n + 1) * H.map star := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro p y hy u v
  have hvalue : ∀ x : ProjectiveCarrier n,
      quaternionicConstraint n (quotientOrbitProjector n x) = 0 := by
    intro x
    induction x using Quotient.inductionOn' with
    | _ z =>
      change orbitProjector n z * CompactSymplecticHaar.standardJ (n + 1) -
        CompactSymplecticHaar.standardJ (n + 1) * (orbitProjector n z).map star = 0
      exact sub_eq_zero.mpr (orbitProjector_commutes_quaternionicJ n z)
  have hder := actual_chartHessian_linear_constraint hLee hDesc hImm
    n d e q g a hq hn (quaternionicConstraint n) hvalue p y hy u v
  dsimp [quaternionicConstraint] at hder
  exact sub_eq_zero.mp hder

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongHessianConstraints
