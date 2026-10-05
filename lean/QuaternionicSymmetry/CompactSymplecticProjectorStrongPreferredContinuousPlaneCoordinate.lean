import QuaternionicSymmetry.CompactSymplecticProjectorStrongPreferredPlaneCoordinate
import QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameQuaternionicSpanBridge
import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeChartSource
import QuaternionicSymmetry.ManifoldAdjointForgetSubmodule

/-! The local continuous I/J/K projector plane is exactly the preferred
continuous quotient Q-plane transported by the actual strong tangent-core
adjoint coordinate change. This is the model-specific premise for the
source-free cocycle gluing theorem. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongPreferredContinuousPlaneCoordinate

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorQuotientImaginaryPlane
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanGaugeSpan
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeSection
open CompactSymplecticProjectorStrongGaugeChartSource
open CompactSymplecticProjectorStrongFrameQuaternionicSpan
open CompactSymplecticProjectorStrongFrameQuaternionicSpanBridge
open CompactSymplecticProjectorStrongPreferredPlaneCoordinate
open CompactSymplecticProjectorPreferredContinuousPlane
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldAdjointForgetNaturality
open ManifoldAdjointForgetSubmodule
open VectorBundleFrameTransitions
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxRecDepth 4000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem localContinuousPlane_eq_core_transport
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
    Submodule.span ℝ (Set.range
      (localQuaternionicGenerator hLee hDesc hImm n d e q g a hq hn x y)) =
      Submodule.map
        ((transitionAtlas (tangentBundleCore 𝓘(ℝ, EModel q)
          (ProjectiveCarrier n))).adjointCoordChange
            (achart (EModel q) y) (achart (EModel q) x) y).toLinearMap
        (preferredContinuousImaginaryPlane hDesc hImm n d e q g a hq hn y) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold
    hLee hDesc hImm n d e q g a hq hn
  letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
    (strongEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn).of_le (by norm_cast)
  let Z := tangentBundleCore 𝓘(ℝ, EModel q) (ProjectiveCarrier n)
  let L := Submodule.span ℝ (Set.range
    (localQuaternionicGenerator hLee hDesc hImm n d e q g a hq hn x y))
  let P := preferredContinuousImaginaryPlane hDesc hImm n d e q g a hq hn y
  obtain ⟨D, hD, hEnd⟩ := localPlane_eq_preferred_conjugate
    hLee hDesc hImm n d e q g a hq hn x y hy
  have hi : y ∈ Z.baseSet (achart (EModel q) y) := Z.mem_baseSet_at y
  have hj : y ∈ Z.baseSet (achart (EModel q) x) := by
    simpa only [Z, tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ, EModel q)] using
      mem_strongGauge_extendedChart_source hLee hDesc hImm n d e q g a hq hn x y hy
  have hForgetBridge : Submodule.map (forgetEnd (V := EModel q)) L =
      euclideanLocalFrameSpan hDesc hImm n d e q g a hq
        (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x) x y := by
    simpa only [L, forgetEnd, forgetContinuousEnd] using
      localContinuousSpan_eq_actualPlane hLee hDesc hImm n d e q g a hq hn x y
  have hForgetPref : Submodule.map (forgetEnd (V := EModel q)) P =
      (quotientImaginaryPlane hDesc hImm n d e q g a hq hn y).map
        (((euclideanModelEquiv q).toLinearEquiv.conjAlgEquiv ℝ).toLinearMap) := by
    simpa only [P, forgetEnd, forgetContinuousEnd] using
      forget_preferredContinuousImaginaryPlane hDesc hImm n d e q g a hq hn y
  have hForgetTransport := forget_map_adjoint Z
    (achart (EModel q) y) (achart (EModel q) x) y hi hj D hD P
  have hImage : Submodule.map (forgetEnd (V := EModel q)) L =
      Submodule.map (forgetEnd (V := EModel q))
        (Submodule.map ((transitionAtlas Z).adjointCoordChange
          (achart (EModel q) y) (achart (EModel q) x) y).toLinearMap P) := by
    rw [hForgetBridge, hForgetTransport, hForgetPref]
    exact hEnd
  have hInject : Function.Injective (forgetEnd (V := EModel q)) := by
    intro S T h
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun A : Module.End ℝ (EModel q) => A v) h
  exact (Submodule.map_injective_of_injective hInject) hImage

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongPreferredContinuousPlaneCoordinate
