import QuaternionicSymmetry.CompactSymplecticProjectorTranslationTangentEquiv
import Mathlib.Algebra.Algebra.Equiv

/-! Transport the checked rank-three imaginary tangent plane to every
coset represented by an actual compact-symplectic matrix. Independence
from the representative and smoothness are separate next steps. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTranslatedImaginaryPlane

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseImaginaryPlane
open CompactSymplecticProjectorBaseImaginaryRank
open CompactSymplecticProjectorTranslationTangentEquiv
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

/-- Push the actual base Q-plane through the genuine derivative of left
translation by `u`; no chart-independent quotient choice is made here. -/
def translatedImaginaryPlane
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (u : G n) :
    letI := atlas.quotientCharts
    Submodule ℝ (Module.End ℝ
      (TangentSpace 𝓘(ℝ, RModel q) (leftCosetAction n u (baseCoset n)))) := by
  letI := atlas.quotientCharts
  let L := (translationTangentEquiv n d e q g atlas u (baseCoset n)).toLinearEquiv
  exact (baseImaginaryPlane hDesc hImm n d e q g atlas hq).map
    (L.conjAlgEquiv ℝ).toLinearMap

/-- Every transported plane still has actual real rank three. -/
theorem translatedImaginaryPlane_finrank
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (u : G n) :
    letI := atlas.quotientCharts
    Module.finrank ℝ
      (translatedImaginaryPlane hDesc hImm n d e q g atlas hq u) = 3 := by
  letI := atlas.quotientCharts
  let L := (translationTangentEquiv n d e q g atlas u (baseCoset n)).toLinearEquiv
  let Q := baseImaginaryPlane hDesc hImm n d e q g atlas hq
  let f := (L.conjAlgEquiv ℝ).toLinearMap
  let fk : Q →ₗ[ℝ] Module.End ℝ
      (TangentSpace 𝓘(ℝ, RModel q) (leftCosetAction n u (baseCoset n))) :=
    f.comp Q.subtype
  have hfk : Function.Injective fk :=
    (L.conjAlgEquiv ℝ).injective.comp Subtype.val_injective
  have hrange : LinearMap.range fk = translatedImaginaryPlane hDesc hImm n d e q g atlas hq u := by
    ext S
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r.1, r.2, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, rfl⟩
  rw [← hrange, LinearMap.finrank_range_of_inj hfk]
  exact baseImaginaryPlane_finrank hDesc hImm n d e q g atlas hq hn

end
end QuaternionicSymmetry.CompactSymplecticProjectorTranslatedImaginaryPlane
