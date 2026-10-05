import QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameGeneratorConjugation
import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanGaugeSpan
import QuaternionicSymmetry.VectorBundleFrameTransitions

/-! The local rank-three projector-tangent plane is exactly the image of
the fixed standard quaternionic I/J/K span under conjugation by the
proved smooth strong-chart frame and its inverse. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameQuaternionicSpan

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorBaseStandardQuaternionicStructure
open CompactSymplecticProjectorEuclideanGaugeSpan
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeSection
open CompactSymplecticProjectorStrongOrthonormalCoordinateFrame
open CompactSymplecticProjectorStrongFrameGeneratorConjugation
open CompactSymplecticProjectorAdaptedAtlasEuclideanGauge
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open VectorBundleFrameTransitions
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxRecDepth 4000

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

def localFrameConjugation
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n) :
    (EModel q →L[ℝ] EModel q) →ₗ[ℝ] (EModel q →L[ℝ] EModel q) where
  toFun S := ((localOrthonormalFromFrame hLee hDesc hImm n d e q g a hq hn x y).comp S).comp
    (localOrthonormalToFrame hLee hDesc hImm n d e q g a hq hn x y)
  map_add' S T := by ext v; simp
  map_smul' r S := by ext v; simp

theorem localFrameConjugation_apply
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n)
    (S : EModel q →L[ℝ] EModel q) :
    localFrameConjugation hLee hDesc hImm n d e q g a hq hn x y S =
      ((localOrthonormalFromFrame hLee hDesc hImm n d e q g a hq hn x y).comp S).comp
        (localOrthonormalToFrame hLee hDesc hImm n d e q g a hq hn x y) := by
  rfl

def localQuaternionicGenerator
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n) :
    letI := a.quotientCharts
    Fin 3 → EModel q →L[ℝ] EModel q := by
  letI := a.quotientCharts
  let σ := strongGaugeSection hLee hDesc hImm n d e q g a hq hn x
  exact ![
    euclideanLocalConjugateOperator n d e q g a σ x
      (Module.End.toContinuousLinearMap (RModel q)
        (baseI hDesc hImm n d e q g a hq).toLinearMap) y,
    euclideanLocalConjugateOperator n d e q g a σ x
      (Module.End.toContinuousLinearMap (RModel q)
        (baseJ hDesc hImm n d e q g a hq).toLinearMap) y,
    euclideanLocalConjugateOperator n d e q g a σ x
      (Module.End.toContinuousLinearMap (RModel q)
        (baseK hDesc hImm n d e q g a hq).toLinearMap) y]

theorem localFrameConjugation_quaternionicSpan
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n)
    (hy : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) :
    letI := a.quotientCharts
    Submodule.map
      (localFrameConjugation hLee hDesc hImm n d e q g a hq hn x y)
      (quaternionicSpan (standardRealQuaternionicStructure n q hq)) =
      Submodule.span ℝ (Set.range
        (localQuaternionicGenerator hLee hDesc hImm n d e q g a hq hn x y)) := by
  letI := a.quotientCharts
  rw [quaternionicSpan, Submodule.map_span]
  have hRange :
      (localFrameConjugation hLee hDesc hImm n d e q g a hq hn x y) ''
          Set.range (quaternionicGenerator (standardRealQuaternionicStructure n q hq)) =
        Set.range ((localFrameConjugation hLee hDesc hImm n d e q g a hq hn x y) ∘
          quaternionicGenerator (standardRealQuaternionicStructure n q hq)) := by
    ext S
    simp only [Set.mem_image, Set.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨T, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨_, ⟨t, rfl⟩, rfl⟩
  rw [hRange]
  congr 1
  apply congrArg Set.range
  funext t
  fin_cases t
  · simpa [Function.comp_apply, quaternionicGenerator,
      localQuaternionicGenerator, localFrameConjugation_apply] using
      (localI_eq_frame_conjugate hLee hDesc hImm n d e q g a hq hn x y hy).symm
  · simpa [Function.comp_apply, quaternionicGenerator,
      localQuaternionicGenerator, localFrameConjugation_apply] using
      (localJ_eq_frame_conjugate hLee hDesc hImm n d e q g a hq hn x y hy).symm
  · simpa [Function.comp_apply, quaternionicGenerator,
      localQuaternionicGenerator, localFrameConjugation_apply] using
      (localK_eq_frame_conjugate hLee hDesc hImm n d e q g a hq hn x y hy).symm

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameQuaternionicSpan
