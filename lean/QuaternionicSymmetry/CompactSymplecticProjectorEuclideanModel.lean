import QuaternionicSymmetry.CompactSymplecticProjectorActualSmoothQuaternionicPlane
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The selected quotient atlas admits an equivalent Euclidean inner-
product model, without changing the quotient topology or chosen charts. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorEuclideanModel

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

def euclideanModelEquiv (q : ℕ) : RModel q ≃L[ℝ] EModel q :=
  (EuclideanSpace.equiv (Fin q) ℝ).symm

def euclideanModel (q : ℕ) : ModelWithCorners ℝ (EModel q) (RModel q) :=
  (𝓘(ℝ, RModel q)).transContinuousLinearEquiv (euclideanModelEquiv q)

theorem euclideanModel_isManifold
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := a.quotientCharts
    IsManifold (euclideanModel q) ∞ (ProjectiveCarrier n) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  change IsManifold ((𝓘(ℝ, RModel q)).transContinuousLinearEquiv
    (euclideanModelEquiv q)) ∞ (ProjectiveCarrier n)
  exact inferInstance

/-- Identity diffeomorphism between the original Pi/sup-norm quotient
model and its Euclidean/L² model. -/
def euclideanModelDiffeomorph
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := a.quotientCharts
    Diffeomorph 𝓘(ℝ, RModel q) (euclideanModel q)
      (ProjectiveCarrier n) (ProjectiveCarrier n) ∞ := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  change Diffeomorph 𝓘(ℝ, RModel q)
    ((𝓘(ℝ, RModel q)).transContinuousLinearEquiv (euclideanModelEquiv q))
    (ProjectiveCarrier n) (ProjectiveCarrier n) ∞
  exact (euclideanModelEquiv q).toTransContinuousLinearEquiv
    (I := 𝓘(ℝ, RModel q)) (M := ProjectiveCarrier n) (n := ∞)

end
end QuaternionicSymmetry.CompactSymplecticProjectorEuclideanModel
