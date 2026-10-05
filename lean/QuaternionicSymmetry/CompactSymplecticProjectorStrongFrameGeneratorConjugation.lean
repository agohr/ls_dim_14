import QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameQuaternionicK

/-! Exact local I/J/K conjugation by the same smooth metric-orthonormal
frame. These equations, rather than an opaque model-Q assumption, will
give the quaternionic span of the actual adapted tangent core. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameGeneratorConjugation

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorBaseStandardQuaternionicStructure
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeSection
open CompactSymplecticProjectorStrongOrthonormalCoordinateFrame
open CompactSymplecticProjectorStrongFrameQuaternionicGenerators
open CompactSymplecticProjectorStrongFrameQuaternionicK
open CompactSymplecticProjectorAdaptedAtlasEuclideanGauge
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxRecDepth 4000

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

private theorem conjugation_of_intertwining {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L T F Fi : V →L[ℝ] V)
    (hFFi : F.comp Fi = ContinuousLinearMap.id ℝ V)
    (hInter : ∀ v, L (F v) = F (T v)) :
    L = (F.comp T).comp Fi := by
  ext z
  have hz := congrArg (fun A : V →L[ℝ] V => A z) hFFi
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hz
  change L z = F (T (Fi z))
  calc
    L z = L (F (Fi z)) := congrArg L hz.symm
    _ = F (T (Fi z)) := hInter (Fi z)

theorem localI_eq_frame_conjugate
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n)
    (hy : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) :
    letI := a.quotientCharts
    euclideanLocalConjugateOperator n d e q g a
      (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x) x
      (Module.End.toContinuousLinearMap (RModel q)
        (baseI hDesc hImm n d e q g a hq).toLinearMap) y =
      ((localOrthonormalFromFrame hLee hDesc hImm n d e q g a hq hn x y).comp
        ((standardRealQuaternionicStructure n q hq).I : EModel q →L[ℝ] EModel q)).comp
        (localOrthonormalToFrame hLee hDesc hImm n d e q g a hq hn x y) := by
  letI := a.quotientCharts
  exact conjugation_of_intertwining _ _ _ _
    (localOrthonormalFrames_inverse hLee hDesc hImm n d e q g a hq hn x y hy).2
    (localFrame_intertwines_I hLee hDesc hImm n d e q g a hq hn x y hy)

theorem localJ_eq_frame_conjugate
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n)
    (hy : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) :
    letI := a.quotientCharts
    euclideanLocalConjugateOperator n d e q g a
      (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x) x
      (Module.End.toContinuousLinearMap (RModel q)
        (baseJ hDesc hImm n d e q g a hq).toLinearMap) y =
      ((localOrthonormalFromFrame hLee hDesc hImm n d e q g a hq hn x y).comp
        ((standardRealQuaternionicStructure n q hq).J : EModel q →L[ℝ] EModel q)).comp
        (localOrthonormalToFrame hLee hDesc hImm n d e q g a hq hn x y) := by
  letI := a.quotientCharts
  exact conjugation_of_intertwining _ _ _ _
    (localOrthonormalFrames_inverse hLee hDesc hImm n d e q g a hq hn x y hy).2
    (localFrame_intertwines_J hLee hDesc hImm n d e q g a hq hn x y hy)

theorem localK_eq_frame_conjugate
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n)
    (hy : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) :
    letI := a.quotientCharts
    euclideanLocalConjugateOperator n d e q g a
      (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x) x
      (Module.End.toContinuousLinearMap (RModel q)
        (baseK hDesc hImm n d e q g a hq).toLinearMap) y =
      ((localOrthonormalFromFrame hLee hDesc hImm n d e q g a hq hn x y).comp
        ((standardRealQuaternionicStructure n q hq).K : EModel q →L[ℝ] EModel q)).comp
        (localOrthonormalToFrame hLee hDesc hImm n d e q g a hq hn x y) := by
  letI := a.quotientCharts
  exact conjugation_of_intertwining _ _ _ _
    (localOrthonormalFrames_inverse hLee hDesc hImm n d e q g a hq hn x y hy).2
    (localFrame_intertwines_K hLee hDesc hImm n d e q g a hq hn x y hy)

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameGeneratorConjugation
