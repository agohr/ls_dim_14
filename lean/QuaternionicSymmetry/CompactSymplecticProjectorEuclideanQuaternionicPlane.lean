import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanRiemannianMetric
import QuaternionicSymmetry.CompactSymplecticProjectorQuotientImaginaryPlane

/-! Transport the actual descended quaternionic tangent plane through
the checked identity diffeomorphism to the Euclidean/L² model. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorEuclideanQuaternionicPlane

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorQuotientImaginaryPlane
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 5000000

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

def euclideanTangentEquiv
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    TangentSpace 𝓘(ℝ, RModel q) x ≃L[ℝ]
      TangentSpace (euclideanModel q) x := by
  letI := a.quotientCharts
  let Φ := euclideanModelDiffeomorph n d e q g a
  have hΦx : Φ x = x := rfl
  simpa only [hΦx] using
    Φ.mfderivToContinuousLinearEquiv (by simp : (∞ : WithTop ℕ∞) ≠ 0) x

def euclideanQuotientImaginaryPlane
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    Submodule ℝ (Module.End ℝ (TangentSpace (euclideanModel q) x)) := by
  letI := a.quotientCharts
  exact (quotientImaginaryPlane hDesc hImm n d e q g a hq hn x).map
    (((euclideanTangentEquiv n d e q g a x).toLinearEquiv.conjAlgEquiv ℝ).toLinearMap)

theorem euclideanQuotientImaginaryPlane_finrank
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    Module.finrank ℝ
      (euclideanQuotientImaginaryPlane hDesc hImm n d e q g a hq hn x) = 3 := by
  letI := a.quotientCharts
  let Q := quotientImaginaryPlane hDesc hImm n d e q g a hq hn x
  let L := (euclideanTangentEquiv n d e q g a x).toLinearEquiv
  let f := (L.conjAlgEquiv ℝ).toLinearMap
  let fk : Q →ₗ[ℝ] Module.End ℝ (TangentSpace (euclideanModel q) x) :=
    f.comp Q.subtype
  have hfk : Function.Injective fk := (L.conjAlgEquiv ℝ).injective.comp Subtype.val_injective
  have hrange : LinearMap.range fk =
      euclideanQuotientImaginaryPlane hDesc hImm n d e q g a hq hn x := by
    ext S
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r.1, r.2, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, rfl⟩
  rw [← hrange, LinearMap.finrank_range_of_inj hfk]
  exact quotientImaginaryPlane_finrank hDesc hImm n d e q g a hq hn x

end
end QuaternionicSymmetry.CompactSymplecticProjectorEuclideanQuaternionicPlane
