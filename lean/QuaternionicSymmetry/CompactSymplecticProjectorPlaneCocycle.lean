import QuaternionicSymmetry.CompactSymplecticProjectorTranslationTangentCocycle
import QuaternionicSymmetry.CompactSymplecticProjectorStabilizerTransport

/-! Functoriality of the genuine rank-three tangent plane transport
under the actual compact-symplectic quotient action. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorPlaneCocycle

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseImaginaryPlane
open CompactSymplecticProjectorTranslatedImaginaryPlane
open CompactSymplecticProjectorTranslationTangentEquiv
open CompactSymplecticProjectorTranslationTangentCocycle
open CompactSymplecticProjectorStabilizerTransport
open CompactSymplecticProjectorIsotropyBlocks
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 5000000

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

private theorem conjAlgEquiv_trans
    {V W X : Type*}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    [AddCommGroup X] [Module ℝ X]
    (A : V ≃ₗ[ℝ] W) (B : W ≃ₗ[ℝ] X) :
    (A.trans B).conjAlgEquiv ℝ =
      (A.conjAlgEquiv ℝ).trans (B.conjAlgEquiv ℝ) := by
  ext F v
  rfl

theorem translatedImaginaryPlane_mul
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (u v : G n) :
    letI := atlas.quotientCharts
    translatedImaginaryPlane hDesc hImm n d e q g atlas hq (u * v) =
      (translatedImaginaryPlane hDesc hImm n d e q g atlas hq v).map
        (((translationTangentEquiv n d e q g atlas u
          (leftCosetAction n v (baseCoset n))).toLinearEquiv.conjAlgEquiv ℝ).toLinearMap) := by
  letI := atlas.quotientCharts
  let A := (translationTangentEquiv n d e q g atlas v (baseCoset n)).toLinearEquiv
  let B := (translationTangentEquiv n d e q g atlas u
    (leftCosetAction n v (baseCoset n))).toLinearEquiv
  have hAB : (translationTangentEquiv n d e q g atlas (u * v)
      (baseCoset n)).toLinearEquiv = A.trans B := by
    apply LinearEquiv.ext
    intro z
    exact congrArg (fun F => F z)
      (translationTangentEquiv_mul n d e q g atlas u v (baseCoset n))
  change (baseImaginaryPlane hDesc hImm n d e q g atlas hq).map
      (((translationTangentEquiv n d e q g atlas (u * v)
        (baseCoset n)).toLinearEquiv.conjAlgEquiv ℝ).toLinearMap) =
    ((baseImaginaryPlane hDesc hImm n d e q g atlas hq).map
      (A.conjAlgEquiv ℝ).toLinearMap).map (B.conjAlgEquiv ℝ).toLinearMap
  rw [hAB, conjAlgEquiv_trans]
  ext S
  constructor
  · rintro ⟨R, hR, hRS⟩
    exact ⟨(A.conjAlgEquiv ℝ) R, ⟨R, hR, rfl⟩, hRS⟩
  · rintro ⟨R, ⟨R₀, hR₀, hRR⟩, hRS⟩
    exact ⟨R₀, hR₀, by rw [← hRR] at hRS; exact hRS⟩

/-- The transported plane is independent of right multiplication by an
actual element of the projector stabilizer. -/
theorem translatedImaginaryPlane_mul_stabilizer
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (u : G n) (k : firstPairStabilizer n) :
    letI := atlas.quotientCharts
    translatedImaginaryPlane hDesc hImm n d e q g atlas hq (u * k.1) =
      translatedImaginaryPlane hDesc hImm n d e q g atlas hq u := by
  letI := atlas.quotientCharts
  rw [translatedImaginaryPlane_mul hDesc hImm n d e q g atlas hq u k.1]
  rw [stabilizer_fixes_baseCoset n k.1 k.2]
  rw [translatedImaginaryPlane_stabilizer hDesc hImm n d e q g atlas hq hn k]
  rfl

/-- The rank-three tangent plane attached to a representative depends
only on its actual quotient point. -/
theorem translatedImaginaryPlane_eq_of_coset_eq
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (u v : G n)
    (huv : (u : ProjectiveCarrier n) = (v : ProjectiveCarrier n)) :
    letI := atlas.quotientCharts
    translatedImaginaryPlane hDesc hImm n d e q g atlas hq u =
      translatedImaginaryPlane hDesc hImm n d e q g atlas hq v := by
  letI := atlas.quotientCharts
  have hk : u⁻¹ * v ∈ firstPairStabilizer n :=
    QuotientGroup.leftRel_apply.mp (Quotient.exact' huv)
  let k : firstPairStabilizer n := ⟨u⁻¹ * v, hk⟩
  have hmul : u * k.1 = v := by
    simp [k]
  calc
    translatedImaginaryPlane hDesc hImm n d e q g atlas hq u =
        translatedImaginaryPlane hDesc hImm n d e q g atlas hq (u * k.1) :=
      (translatedImaginaryPlane_mul_stabilizer hDesc hImm n d e q g atlas hq hn u k).symm
    _ = translatedImaginaryPlane hDesc hImm n d e q g atlas hq v := by rw [hmul]

end
end QuaternionicSymmetry.CompactSymplecticProjectorPlaneCocycle
