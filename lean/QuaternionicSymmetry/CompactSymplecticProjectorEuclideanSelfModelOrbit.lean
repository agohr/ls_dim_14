import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanChartBridge

/-! Smooth projector orbit and injective differential on the genuine
Euclidean-valued quotient chart atlas. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorEuclideanSelfModelOrbit

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorEuclideanChartBridge
open CompactSymplecticProjectorEuclideanModelSmoothOrbit
open CompactSymplecticProjectorEuclideanModelImmersion
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 5000000

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem smooth_quotientOrbitProjector_selfModel
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := euclideanQuotientCharts n d e q g a
    ContMDiff 𝓘(ℝ, EModel q) 𝓘(ℝ, Mat n) ∞
      (quotientOrbitProjector n) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := euclideanModel_isManifold n d e q g a
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  have h := (smooth_quotientOrbitProjector_euclideanModel hDesc n d e q g a).comp
    (euclideanChartDiffeomorph n d e q g a).symm.contMDiff
  simpa [Function.comp_def, euclideanChartDiffeomorph] using h

theorem quotientOrbitProjector_mfderiv_injective_selfModel
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := euclideanQuotientCharts n d e q g a
    Function.Injective
      (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := euclideanModel_isManifold n d e q g a
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  let Φ := euclideanChartDiffeomorph n d e q g a
  have hΦx : Φ x = x := rfl
  let D : TangentSpace (euclideanModel q) x ≃L[ℝ]
      TangentSpace 𝓘(ℝ, EModel q) x := by
    simpa only [hΦx] using
      Φ.mfderivToContinuousLinearEquiv (by simp : (∞ : WithTop ℕ∞) ≠ 0) x
  have hOld := quotientOrbitProjector_mfderiv_injective_euclideanModel
    hDesc hImm n d e q g a x
  have hNewSmooth := smooth_quotientOrbitProjector_selfModel hDesc n d e q g a
  have hComp : mfderiv (euclideanModel q) 𝓘(ℝ, Mat n)
      (quotientOrbitProjector n) x =
      (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x).comp (D : _ →L[ℝ] _) := by
    have h := mfderiv_comp x
      (hNewSmooth.mdifferentiableAt (by simp))
      (Φ.contMDiff_toFun.mdifferentiableAt (by simp))
    simpa only [Function.comp_def, hΦx, D,
      Diffeomorph.mfderivToContinuousLinearEquiv_coe] using h
  intro u v huv
  have huv' : mfderiv (euclideanModel q) 𝓘(ℝ, Mat n)
      (quotientOrbitProjector n) x (D.symm u) =
      mfderiv (euclideanModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x (D.symm v) := by
    rw [hComp]
    change (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, Mat n)
      (quotientOrbitProjector n) x) (D (D.symm u)) =
      (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x) (D (D.symm v))
    rw [D.apply_symm_apply, D.apply_symm_apply]
    exact huv
  exact D.symm.injective (hOld huv')

end
end QuaternionicSymmetry.CompactSymplecticProjectorEuclideanSelfModelOrbit
