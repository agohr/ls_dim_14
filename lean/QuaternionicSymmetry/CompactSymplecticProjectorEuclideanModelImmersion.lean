import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanModelSmoothOrbit

/-! Injectivity of the actual projector differential survives the
identity diffeomorphism to the Euclidean/L² tangent model. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorEuclideanModelImmersion

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorSmoothAction
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanModelSmoothOrbit
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 5000000

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev RModel (d : ℕ) := Fin d → ℝ

theorem quotientOrbitProjector_mfderiv_injective_euclideanModel
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    Function.Injective
      (mfderiv (euclideanModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  let Φ := euclideanModelDiffeomorph n d e q g a
  have hΦx : Φ x = x := rfl
  let D : TangentSpace 𝓘(ℝ, RModel q) x ≃L[ℝ]
      TangentSpace (euclideanModel q) x := by
    simpa only [hΦx] using
      Φ.mfderivToContinuousLinearEquiv (by simp : (∞ : WithTop ℕ∞) ≠ 0) x
  have hOld := quotientOrbitProjector_mfderiv_injective hDesc hImm n d e q g a x
  have hNewSmooth := smooth_quotientOrbitProjector_euclideanModel hDesc n d e q g a
  have hComp : mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
      (quotientOrbitProjector n) x =
      (mfderiv (euclideanModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x).comp (D : _ →L[ℝ] _) := by
    have h := mfderiv_comp x
      (hNewSmooth.mdifferentiableAt (by simp))
      (Φ.contMDiff_toFun.mdifferentiableAt (by simp))
    simpa only [Function.comp_def, hΦx, D,
      Diffeomorph.mfderivToContinuousLinearEquiv_coe]
      using h
  intro u v huv
  have huv' : mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
      (quotientOrbitProjector n) x (D.symm u) =
      mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x (D.symm v) := by
    rw [hComp]
    change (mfderiv (euclideanModel q) 𝓘(ℝ, Mat n)
      (quotientOrbitProjector n) x) (D (D.symm u)) =
      (mfderiv (euclideanModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x) (D (D.symm v))
    rw [D.apply_symm_apply, D.apply_symm_apply]
    exact huv
  have h := hOld huv'
  exact D.symm.injective h

end
end QuaternionicSymmetry.CompactSymplecticProjectorEuclideanModelImmersion
