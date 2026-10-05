import QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockSpan
import QuaternionicSymmetry.QuaternionImaginaryConjugation

/-! The checked I/J/K operators on the genuine projector tangent define
an actual real-quaternion algebra action, without imposing an artificial
inner-product instance on the tangent space. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorBaseQuaternionAction

open Manifold
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorFirstBlockSpan
open CompactSymplecticProjectorIsotropyUnits
open CompactSymplecticStabilizerBlockPair
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ

def baseQuaternionBasis
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := atlas.quotientCharts
    QuaternionAlgebra.Basis
      (Module.End ℝ (TangentSpace 𝓘(ℝ, RModel q) (baseCoset n))) (-1 : ℝ) 0 (-1) := by
  letI := atlas.quotientCharts
  let I := baseI hDesc hImm n d e q g atlas hq
  let J := baseJ hDesc hImm n d e q g atlas hq
  let K := baseK hDesc hImm n d e q g atlas hq
  exact {
    i := I.toLinearMap
    j := J.toLinearMap
    k := K.toLinearMap
    i_mul_i := by
      ext v
      simpa [I] using baseI_sq hDesc hImm n d e q g atlas hq v
    j_mul_j := by
      ext v
      simpa [J] using baseJ_sq hDesc hImm n d e q g atlas hq v
    i_mul_j := by ext v; rfl
    j_mul_i := by
      ext v
      have h := baseI_J_anti hDesc hImm n d e q g atlas hq v
      simpa [K, I, J] using (congrArg Neg.neg h).symm
  }

def baseQuaternionAction
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := atlas.quotientCharts
    ℍ →ₐ[ℝ] Module.End ℝ
      (TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)) := by
  letI := atlas.quotientCharts
  exact (baseQuaternionBasis hDesc hImm n d e q g atlas hq).liftHom

theorem baseQuaternionAction_apply
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := atlas.quotientCharts
    ∀ (r : ℍ) (v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)),
      baseQuaternionAction hDesc hImm n d e q g atlas hq r v =
        r.re • v + r.imI • baseI hDesc hImm n d e q g atlas hq v +
        r.imJ • baseJ hDesc hImm n d e q g atlas hq v +
        r.imK • baseK hDesc hImm n d e q g atlas hq v := by
  letI := atlas.quotientCharts
  intro r v
  rfl

/-- Matrix entries of an actual first-block unit, read as the quaternion
whose real-linear action was computed in the preceding checked leaf. -/
def firstBlockQuaternion (A : FirstBlockGroup) : ℍ :=
  ⟨(A.1.1 0 0).re, (A.1.1 0 0).im,
    -(A.1.1 0 1).re, -(A.1.1 0 1).im⟩

theorem firstBlock_derivative_eq_quaternionAction
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (A : FirstBlockGroup) :
    letI := atlas.quotientCharts
    ∀ v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
        (leftCosetAction n (firstBlockLift n A).1) (baseCoset n) v =
      baseQuaternionAction hDesc hImm n d e q g atlas hq
        (firstBlockQuaternion A) v := by
  letI := atlas.quotientCharts
  intro v
  rw [firstBlock_derivative_quaternion_span hDesc hImm n d e q g atlas hq A v,
    baseQuaternionAction_apply]
  simp [firstBlockQuaternion, neg_smul, sub_eq_add_neg]

end
end QuaternionicSymmetry.CompactSymplecticProjectorBaseQuaternionAction
