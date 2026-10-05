import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanSelfModelMetric
import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanQuaternionicPlane

/-! Transport the actual descended imaginary quaternionic tangent plane
to the genuine Euclidean-valued quotient atlas. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorEuclideanSelfModelPlane

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorEuclideanChartBridge
open CompactSymplecticProjectorEuclideanQuaternionicPlane
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

def selfModelTangentEquiv
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := euclideanQuotientCharts n d e q g a
    TangentSpace (euclideanModel q) x ≃L[ℝ]
      TangentSpace 𝓘(ℝ, EModel q) x := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := euclideanModel_isManifold n d e q g a
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  let Φ := euclideanChartDiffeomorph n d e q g a
  have hΦx : Φ x = x := rfl
  simpa only [hΦx] using
    Φ.mfderivToContinuousLinearEquiv (by simp : (∞ : WithTop ℕ∞) ≠ 0) x

def selfModelImaginaryPlane
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := euclideanQuotientCharts n d e q g a
    Submodule ℝ (Module.End ℝ (TangentSpace 𝓘(ℝ, EModel q) x)) := by
  letI := a.quotientCharts
  letI := euclideanQuotientCharts n d e q g a
  exact (euclideanQuotientImaginaryPlane hDesc hImm n d e q g a hq hn x).map
    (((selfModelTangentEquiv n d e q g a x).toLinearEquiv.conjAlgEquiv ℝ).toLinearMap)

theorem selfModelImaginaryPlane_finrank
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := euclideanQuotientCharts n d e q g a
    Module.finrank ℝ
      (selfModelImaginaryPlane hDesc hImm n d e q g a hq hn x) = 3 := by
  letI := a.quotientCharts
  letI := euclideanQuotientCharts n d e q g a
  let Q := euclideanQuotientImaginaryPlane hDesc hImm n d e q g a hq hn x
  let L := (selfModelTangentEquiv n d e q g a x).toLinearEquiv
  let f := (L.conjAlgEquiv ℝ).toLinearMap
  let fk : Q →ₗ[ℝ] Module.End ℝ (TangentSpace 𝓘(ℝ, EModel q) x) :=
    f.comp Q.subtype
  have hfk : Function.Injective fk := (L.conjAlgEquiv ℝ).injective.comp Subtype.val_injective
  have hrange : LinearMap.range fk =
      selfModelImaginaryPlane hDesc hImm n d e q g a hq hn x := by
    ext S
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r.1, r.2, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, rfl⟩
  rw [← hrange, LinearMap.finrank_range_of_inj hfk]
  exact euclideanQuotientImaginaryPlane_finrank hDesc hImm n d e q g a hq hn x

end
end QuaternionicSymmetry.CompactSymplecticProjectorEuclideanSelfModelPlane
