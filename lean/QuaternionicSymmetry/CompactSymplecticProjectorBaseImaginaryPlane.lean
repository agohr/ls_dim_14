import QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockQuaternionUnit

/-! The image of the imaginary quaternions in endomorphisms of the actual
projector tangent is invariant under the checked first-block isotropy
action. Its rank is a separate theorem for positive quaternionic dimension. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorBaseImaginaryPlane

open Manifold
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionAction
open CompactSymplecticProjectorFirstBlockQuaternionUnit
open CompactSymplecticStabilizerBlockPair
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open QuaternionicSymmetry.QuaternionImaginaryConjugation
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 1000000

private abbrev RModel (d : ℕ) := Fin d → ℝ

/-- The image of pure imaginary quaternions under the actual base tangent
algebra action. This is a real-linear subspace, not a postulated bundle. -/
def baseImaginaryPlane
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := atlas.quotientCharts
    Submodule ℝ (Module.End ℝ
      (TangentSpace 𝓘(ℝ, RModel q) (baseCoset n))) := by
  letI := atlas.quotientCharts
  exact ((QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)).ker).map
    (baseQuaternionAction hDesc hImm n d e q g atlas hq).toLinearMap

theorem action_imaginary_mem
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (r : ℍ) (hr : r.re = 0) :
    letI := atlas.quotientCharts
    baseQuaternionAction hDesc hImm n d e q g atlas hq r ∈
      baseImaginaryPlane hDesc hImm n d e q g atlas hq := by
  letI := atlas.quotientCharts
  apply Submodule.mem_map.mpr
  exact ⟨r, (LinearMap.mem_ker).2 hr, rfl⟩

/-- Every actual first-block isotropy element conjugates the pure-imaginary
plane into itself in the genuine tangent endomorphism algebra. -/
theorem firstBlock_conjugates_imaginary
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (A : FirstBlockGroup) :
    letI := atlas.quotientCharts
    ∀ S : baseImaginaryPlane hDesc hImm n d e q g atlas hq,
      baseQuaternionAction hDesc hImm n d e q g atlas hq
        (firstBlockQuaternion A) * S.1 *
        baseQuaternionAction hDesc hImm n d e q g atlas hq
          (firstBlockQuaternion A)⁻¹ ∈
        baseImaginaryPlane hDesc hImm n d e q g atlas hq := by
  letI := atlas.quotientCharts
  intro S
  obtain ⟨r, hr, hSr⟩ := Submodule.mem_map.mp S.2
  have hr0 : r.re = 0 := (LinearMap.mem_ker.mp hr)
  rw [← hSr]
  change baseQuaternionAction hDesc hImm n d e q g atlas hq (firstBlockQuaternion A) *
      baseQuaternionAction hDesc hImm n d e q g atlas hq r *
      baseQuaternionAction hDesc hImm n d e q g atlas hq (firstBlockQuaternion A)⁻¹ ∈
    baseImaginaryPlane hDesc hImm n d e q g atlas hq
  rw [← map_mul, ← map_mul]
  exact action_imaginary_mem hDesc hImm n d e q g atlas hq _
    (imaginary_conjugation (firstBlockQuaternion A) r
      (firstBlockQuaternion_ne_zero A) hr0)

end
end QuaternionicSymmetry.CompactSymplecticProjectorBaseImaginaryPlane
