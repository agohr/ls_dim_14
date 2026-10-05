import QuaternionicSymmetry.CompactSymplecticProjectorActualSmoothQuaternionicPlane

/-! The actual smooth coordinate conjugates satisfy quaternionic
relations pointwise wherever the checked gauge derivative is invertible. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicRelations

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorLocalDerivativeInverseSmooth
open CompactSymplecticProjectorLocalQuaternionicFrameSmooth
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 5000000

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

private def SI
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    RModel q →L[ℝ] RModel q := by
  letI := a.quotientCharts
  exact Module.End.toContinuousLinearMap (RModel q)
    (baseI hDesc hImm n d e q g a hq).toLinearMap

private def SJ
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    RModel q →L[ℝ] RModel q := by
  letI := a.quotientCharts
  exact Module.End.toContinuousLinearMap (RModel q)
    (baseJ hDesc hImm n d e q g a hq).toLinearMap

def localI
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (σ : ProjectiveCarrier n → G n) (x : ProjectiveCarrier n) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    ProjectiveCarrier n → RModel q →L[ℝ] RModel q := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  exact localConjugateOperator n d e q g a σ x (SI hDesc hImm n d e q g a hq)

def localJ
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (σ : ProjectiveCarrier n → G n) (x : ProjectiveCarrier n) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    ProjectiveCarrier n → RModel q →L[ℝ] RModel q := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  exact localConjugateOperator n d e q g a σ x (SJ hDesc hImm n d e q g a hq)

private theorem conjugate_sq (q : ℕ) (E : RModel q ≃L[ℝ] RModel q)
    (S : RModel q →L[ℝ] RModel q) (hs : ∀ v, S (S v) = -v) (v : RModel q) :
    ((E : RModel q →L[ℝ] RModel q).comp
      (S.comp (E.symm : RModel q →L[ℝ] RModel q)))
      (((E : RModel q →L[ℝ] RModel q).comp
        (S.comp (E.symm : RModel q →L[ℝ] RModel q))) v) = -v := by
  change E (S (E.symm (E (S (E.symm v))))) = -v
  rw [E.symm_apply_apply, hs, map_neg, E.apply_symm_apply]

private theorem conjugate_anti (q : ℕ) (E : RModel q ≃L[ℝ] RModel q)
    (S T : RModel q →L[ℝ] RModel q)
    (hst : ∀ v, S (T v) = -T (S v)) (v : RModel q) :
    ((E : RModel q →L[ℝ] RModel q).comp
      (S.comp (E.symm : RModel q →L[ℝ] RModel q)))
      (((E : RModel q →L[ℝ] RModel q).comp
        (T.comp (E.symm : RModel q →L[ℝ] RModel q))) v) =
    -((E : RModel q →L[ℝ] RModel q).comp
      (T.comp (E.symm : RModel q →L[ℝ] RModel q)))
      (((E : RModel q →L[ℝ] RModel q).comp
        (S.comp (E.symm : RModel q →L[ℝ] RModel q))) v) := by
  change E (S (E.symm (E (T (E.symm v))))) =
    -E (T (E.symm (E (S (E.symm v)))))
  rw [E.symm_apply_apply, E.symm_apply_apply, hst, map_neg]

theorem localI_sq
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (σ : ProjectiveCarrier n → G n) (x y : ProjectiveCarrier n) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∀ E : RModel q ≃L[ℝ] RModel q,
      (E : RModel q →L[ℝ] RModel q) =
        gaugeDerivativeCoordinates n d e q g a σ x y →
      ∀ v : RModel q,
        localI hDesc hImm n d e q g a hq σ x y
          (localI hDesc hImm n d e q g a hq σ x y v) = -v := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro E hE v
  have hs : ∀ z : RModel q,
      SI hDesc hImm n d e q g a hq
        (SI hDesc hImm n d e q g a hq z) = -z :=
    baseI_sq hDesc hImm n d e q g a hq
  change ((gaugeDerivativeCoordinates n d e q g a σ x y).comp
      (SI hDesc hImm n d e q g a hq)).comp
      (ContinuousLinearMap.inverse (gaugeDerivativeCoordinates n d e q g a σ x y))
      (((gaugeDerivativeCoordinates n d e q g a σ x y).comp
        (SI hDesc hImm n d e q g a hq)).comp
        (ContinuousLinearMap.inverse (gaugeDerivativeCoordinates n d e q g a σ x y)) v) = -v
  rw [← hE, ContinuousLinearMap.inverse_equiv]
  exact conjugate_sq q E _ hs v

theorem localJ_sq
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (σ : ProjectiveCarrier n → G n) (x y : ProjectiveCarrier n) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∀ E : RModel q ≃L[ℝ] RModel q,
      (E : RModel q →L[ℝ] RModel q) =
        gaugeDerivativeCoordinates n d e q g a σ x y →
      ∀ v : RModel q,
        localJ hDesc hImm n d e q g a hq σ x y
          (localJ hDesc hImm n d e q g a hq σ x y v) = -v := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro E hE v
  have hs : ∀ z : RModel q,
      SJ hDesc hImm n d e q g a hq
        (SJ hDesc hImm n d e q g a hq z) = -z :=
    baseJ_sq hDesc hImm n d e q g a hq
  change ((gaugeDerivativeCoordinates n d e q g a σ x y).comp
      (SJ hDesc hImm n d e q g a hq)).comp
      (ContinuousLinearMap.inverse (gaugeDerivativeCoordinates n d e q g a σ x y))
      (((gaugeDerivativeCoordinates n d e q g a σ x y).comp
        (SJ hDesc hImm n d e q g a hq)).comp
        (ContinuousLinearMap.inverse (gaugeDerivativeCoordinates n d e q g a σ x y)) v) = -v
  rw [← hE, ContinuousLinearMap.inverse_equiv]
  exact conjugate_sq q E _ hs v

theorem localI_J_anti
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (σ : ProjectiveCarrier n → G n) (x y : ProjectiveCarrier n) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∀ E : RModel q ≃L[ℝ] RModel q,
      (E : RModel q →L[ℝ] RModel q) =
        gaugeDerivativeCoordinates n d e q g a σ x y →
      ∀ v : RModel q,
        localI hDesc hImm n d e q g a hq σ x y
          (localJ hDesc hImm n d e q g a hq σ x y v) =
        -localJ hDesc hImm n d e q g a hq σ x y
          (localI hDesc hImm n d e q g a hq σ x y v) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro E hE v
  have hs : ∀ z : RModel q,
      SI hDesc hImm n d e q g a hq
        (SJ hDesc hImm n d e q g a hq z) =
      -SJ hDesc hImm n d e q g a hq
        (SI hDesc hImm n d e q g a hq z) :=
    baseI_J_anti hDesc hImm n d e q g a hq
  change ((gaugeDerivativeCoordinates n d e q g a σ x y).comp
      (SI hDesc hImm n d e q g a hq)).comp
      (ContinuousLinearMap.inverse (gaugeDerivativeCoordinates n d e q g a σ x y))
      (((gaugeDerivativeCoordinates n d e q g a σ x y).comp
        (SJ hDesc hImm n d e q g a hq)).comp
        (ContinuousLinearMap.inverse (gaugeDerivativeCoordinates n d e q g a σ x y)) v) =
    -((gaugeDerivativeCoordinates n d e q g a σ x y).comp
      (SJ hDesc hImm n d e q g a hq)).comp
      (ContinuousLinearMap.inverse (gaugeDerivativeCoordinates n d e q g a σ x y))
      (((gaugeDerivativeCoordinates n d e q g a σ x y).comp
        (SI hDesc hImm n d e q g a hq)).comp
        (ContinuousLinearMap.inverse (gaugeDerivativeCoordinates n d e q g a σ x y)) v)
  rw [← hE, ContinuousLinearMap.inverse_equiv]
  exact conjugate_anti q E _ _ hs v

end
end QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicRelations
