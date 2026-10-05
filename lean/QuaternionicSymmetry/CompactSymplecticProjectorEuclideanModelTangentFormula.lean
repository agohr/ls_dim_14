import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanChartBridgeTangent

/-! The differential of the identity from the original quotient model to
its Euclidean model is exactly the canonical coordinate linear equivalence. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorEuclideanModelTangentFormula

open Manifold
open Filter
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorEuclideanQuaternionicPlane
open CompactSymplecticProjectorEuclideanSelfModelPlane
open CompactSymplecticProjectorEuclideanChartBridgeTangent
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Manifold ContDiff Topology
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem euclideanModelIdentity_mfderiv_eq_linearEquiv
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    mfderiv 𝓘(ℝ, RModel q) (euclideanModel q)
      (id : ProjectiveCarrier n → ProjectiveCarrier n) x =
      (euclideanModelEquiv q).toContinuousLinearMap := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  have h : HasMFDerivAt 𝓘(ℝ, RModel q) (euclideanModel q)
      (id : ProjectiveCarrier n → ProjectiveCarrier n) x
      (euclideanModelEquiv q).toContinuousLinearMap := by
    refine ⟨continuousAt_id, ?_⟩
    have hevent : ∀ᶠ y in 𝓝[Set.range (𝓘(ℝ, RModel q))]
        (extChartAt 𝓘(ℝ, RModel q) x) x,
        (extChartAt (euclideanModel q) x ∘
          (extChartAt 𝓘(ℝ, RModel q) x).symm) y =
          (euclideanModelEquiv q) y := by
      apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin x)
      intro y hy
      simpa only [Function.comp_apply, euclideanModel,
        ModelWithCorners.coe_extChartAt_transContinuousLinearEquiv] using
        congrArg (euclideanModelEquiv q)
          ((extChartAt 𝓘(ℝ, RModel q) x).right_inv hy)
    apply HasFDerivWithinAt.congr_of_eventuallyEq
      (euclideanModelEquiv q).hasFDerivAt.hasFDerivWithinAt hevent
    simpa [euclideanModel, mfld_simps] using congrArg (euclideanModelEquiv q)
      ((extChartAt 𝓘(ℝ, RModel q) x).right_inv
        ((extChartAt 𝓘(ℝ, RModel q) x).map_source (mem_extChartAt_source x)))
  exact h.mfderiv

theorem euclideanTangentEquiv_eq_coordinateEquiv
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    euclideanTangentEquiv n d e q g a x = euclideanModelEquiv q := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  apply ContinuousLinearEquiv.ext
  funext v
  change mfderiv 𝓘(ℝ, RModel q) (euclideanModel q)
    (id : ProjectiveCarrier n → ProjectiveCarrier n) x v =
      (euclideanModelEquiv q) v
  rw [euclideanModelIdentity_mfderiv_eq_linearEquiv n d e q g a x]
  rfl

theorem originalToSelf_tangentEquiv_eq_coordinateEquiv
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := euclideanQuotientCharts n d e q g a
    (euclideanTangentEquiv n d e q g a x).trans
      (selfModelTangentEquiv n d e q g a x) = euclideanModelEquiv q := by
  letI := a.quotientCharts
  letI := euclideanQuotientCharts n d e q g a
  rw [euclideanTangentEquiv_eq_coordinateEquiv n d e q g a x,
    selfModelTangentEquiv_eq_refl n d e q g a x]
  rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorEuclideanModelTangentFormula
