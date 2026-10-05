import QuaternionicSymmetry.CompactSymplecticProjectorBaseTangentRange
import QuaternionicSymmetry.QuaternionicMatrixModel

/-! Quaternionic endomorphisms on the actual base tangent space, transported
through the now-proved complete projector differential coordinates. Metric
compatibility and isotropy-span preservation are separate next steps. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorBaseQuaternionic

open Manifold
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseTangentRange
open CompactSymplecticProjectorQuaternionicUpperLinear
open CompactSymplecticProjectorRiemannianMetric
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev J (n : ℕ) := Fin n ⊕ Fin n
private abbrev RModel (d : ℕ) := Fin d → ℝ

/-- The row-coordinate vector space is linearly the standard complex
coordinate realization of `ℍ^n`. -/
def rowEuclideanEquiv (n : ℕ) :
    (J n → ℂ) ≃ₗ[ℝ] QuaternionicMatrixModel.V n :=
  (WithLp.linearEquiv 2 ℝ (J n → ℂ)).symm

/-- Real-linear coordinates on the genuine base tangent, obtained from the
surjective projector derivative and explicit quaternionic mixed blocks. -/
def baseTangentEuclideanEquiv
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (hq : q = 4 * n) :
    letI := a.quotientCharts
    TangentSpace 𝓘(ℝ, RModel q) (baseCoset n) ≃ₗ[ℝ]
      QuaternionicMatrixModel.V n := by
  letI := a.quotientCharts
  exact (baseTangentUpperLinearEquiv hDesc hImm n d e q g a hq).trans
    ((upperRowLinearEquiv n).trans (rowEuclideanEquiv n))

/-- The first quaternionic tangent endomorphism on the true manifold tangent
space, obtained by conjugating the standard complex multiplication through
the checked projector-differential equivalence. -/
def baseI
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    TangentSpace 𝓘(ℝ, RModel q) (baseCoset n) ≃ₗ[ℝ]
      TangentSpace 𝓘(ℝ, RModel q) (baseCoset n) := by
  letI := a.quotientCharts
  let e := baseTangentEuclideanEquiv hDesc hImm n d e q g a hq
  exact (e.trans (QuaternionicMatrixModel.standardI n).toLinearEquiv).trans e.symm

/-- The second quaternionic tangent endomorphism on the true manifold
tangent space. -/
def baseJ
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    TangentSpace 𝓘(ℝ, RModel q) (baseCoset n) ≃ₗ[ℝ]
      TangentSpace 𝓘(ℝ, RModel q) (baseCoset n) := by
  letI := a.quotientCharts
  let e := baseTangentEuclideanEquiv hDesc hImm n d e q g a hq
  exact (e.trans (QuaternionicMatrixModel.standardJ n).toLinearEquiv).trans e.symm

/-- The third operator is the checked quaternionic product `I ∘ J`. -/
def baseK
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    TangentSpace 𝓘(ℝ, RModel q) (baseCoset n) ≃ₗ[ℝ]
      TangentSpace 𝓘(ℝ, RModel q) (baseCoset n) := by
  letI := a.quotientCharts
  exact (baseJ hDesc hImm n d e q g a hq).trans
    (baseI hDesc hImm n d e q g a hq)

private theorem transported_sq
    {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (e : V ≃ₗ[ℝ] W) (A : W ≃ₗ[ℝ] W)
    (hA : ∀ w, A (A w) = -w) (v : V) :
    ((e.trans A).trans e.symm) (((e.trans A).trans e.symm) v) = -v := by
  apply e.injective
  simp only [LinearEquiv.trans_apply, e.apply_symm_apply, hA, map_neg,
    e.symm_apply_apply]

private theorem transported_anti
    {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (e : V ≃ₗ[ℝ] W) (A B : W ≃ₗ[ℝ] W)
    (hAB : ∀ w, A (B w) = -B (A w)) (v : V) :
    ((e.trans A).trans e.symm) (((e.trans B).trans e.symm) v) =
      -((e.trans B).trans e.symm) (((e.trans A).trans e.symm) v) := by
  apply e.injective
  simp only [LinearEquiv.trans_apply, e.apply_symm_apply, hAB, map_neg]

/-- The first actual tangent operator squares to negative identity. -/
theorem baseI_sq
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    ∀ v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      baseI hDesc hImm n d e q g a hq
        (baseI hDesc hImm n d e q g a hq v) = -v := by
  letI := a.quotientCharts
  intro v
  let e := baseTangentEuclideanEquiv hDesc hImm n d e q g a hq
  change ((e.trans (QuaternionicMatrixModel.standardI n).toLinearEquiv).trans e.symm)
      (((e.trans (QuaternionicMatrixModel.standardI n).toLinearEquiv).trans e.symm) v) = -v
  exact transported_sq e (QuaternionicMatrixModel.standardI n).toLinearEquiv
    (QuaternionicMatrixModel.standardQuaternionicStructure n).I_sq v

/-- The second actual tangent operator squares to negative identity. -/
theorem baseJ_sq
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    ∀ v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      baseJ hDesc hImm n d e q g a hq
        (baseJ hDesc hImm n d e q g a hq v) = -v := by
  letI := a.quotientCharts
  intro v
  let e := baseTangentEuclideanEquiv hDesc hImm n d e q g a hq
  change ((e.trans (QuaternionicMatrixModel.standardJ n).toLinearEquiv).trans e.symm)
      (((e.trans (QuaternionicMatrixModel.standardJ n).toLinearEquiv).trans e.symm) v) = -v
  exact transported_sq e (QuaternionicMatrixModel.standardJ n).toLinearEquiv
    (QuaternionicMatrixModel.standardQuaternionicStructure n).J_sq v

/-- The two genuine tangent operators anticommute, so their product `K`
is the third quaternionic direction. -/
theorem baseI_J_anti
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    ∀ v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      baseI hDesc hImm n d e q g a hq
        (baseJ hDesc hImm n d e q g a hq v) =
      -baseJ hDesc hImm n d e q g a hq
        (baseI hDesc hImm n d e q g a hq v) := by
  letI := a.quotientCharts
  intro v
  let e := baseTangentEuclideanEquiv hDesc hImm n d e q g a hq
  change ((e.trans (QuaternionicMatrixModel.standardI n).toLinearEquiv).trans e.symm)
      (((e.trans (QuaternionicMatrixModel.standardJ n).toLinearEquiv).trans e.symm) v) =
    -((e.trans (QuaternionicMatrixModel.standardJ n).toLinearEquiv).trans e.symm)
      (((e.trans (QuaternionicMatrixModel.standardI n).toLinearEquiv).trans e.symm) v)
  exact transported_anti e (QuaternionicMatrixModel.standardI n).toLinearEquiv
    (QuaternionicMatrixModel.standardJ n).toLinearEquiv
    (QuaternionicMatrixModel.standardQuaternionicStructure n).I_J_anti v

end
end QuaternionicSymmetry.CompactSymplecticProjectorBaseQuaternionic
