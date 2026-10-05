import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeFrame
import QuaternionicSymmetry.CompactSymplecticProjectorPreferredContinuousPlane
import QuaternionicSymmetry.LinearConjugationSubmoduleNaturality

/-! On one selected strong chart, the actual projector Q-plane is the
preferred Euclidean quotient Q-plane conjugated by the very tangent-core
coordinate transition from the point's chart to the selected chart. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongPreferredPlaneCoordinate

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorQuotientImaginaryPlane
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanGaugeSpan
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeSection
open CompactSymplecticProjectorStrongGaugeFrame
open CompactSymplecticProjectorPreferredContinuousPlane
open LinearConjugationSubmoduleNaturality
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxRecDepth 4000

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem localPlane_eq_preferred_conjugate
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n)
    (hy : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn
    ∃ D : EModel q ≃L[ℝ] EModel q,
      (D : EModel q →L[ℝ] EModel q) =
        (tangentBundleCore 𝓘(ℝ, EModel q) (ProjectiveCarrier n)).coordChange
          (achart (EModel q) y) (achart (EModel q) x) y ∧
      euclideanLocalFrameSpan hDesc hImm n d e q g a hq
          (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x) x y =
        ((quotientImaginaryPlane hDesc hImm n d e q g a hq hn y).map
          (((euclideanModelEquiv q).toLinearEquiv.conjAlgEquiv ℝ).toLinearMap)).map
          ((D.toLinearEquiv.conjAlgEquiv ℝ).toLinearMap) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold
    hLee hDesc hImm n d e q g a hq hn
  obtain ⟨C, hPlane, hCore⟩ := strongGaugeFrame_span_and_core_at_points
    hLee hDesc hImm n d e q g a hq hn x y hy
  let U := euclideanModelEquiv q
  let D : EModel q ≃L[ℝ] EModel q := (U.symm.trans C).trans U
  have hD : (D : EModel q →L[ℝ] EModel q) =
      (tangentBundleCore 𝓘(ℝ, EModel q) (ProjectiveCarrier n)).coordChange
        (achart (EModel q) y) (achart (EModel q) x) y := by
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L : EModel q →L[ℝ] EModel q => L v) hCore
  have hSquare : C.toLinearEquiv.trans U.toLinearEquiv =
      U.toLinearEquiv.trans D.toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    simp [D, U]
  have hNat := submodule_map_conj_commutes U.toLinearEquiv C.toLinearEquiv
    D.toLinearEquiv hSquare
    (quotientImaginaryPlane hDesc hImm n d e q g a hq hn y)
  refine ⟨D, hD, ?_⟩
  exact hPlane.trans hNat

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongPreferredPlaneCoordinate
