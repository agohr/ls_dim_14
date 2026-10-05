import QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameQuaternionicSpan

/-! Passing from continuous endomorphisms to their underlying real-linear
endomorphisms identifies the strong-frame I/J/K span with the already
constructed actual Euclidean local projector Q-plane. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameQuaternionicSpanBridge

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorEuclideanGaugeSpan
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeSection
open CompactSymplecticProjectorStrongFrameQuaternionicSpan
open CompactSymplecticProjectorAdaptedAtlasEuclideanGauge
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxRecDepth 4000

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

def forgetContinuousEnd (q : ℕ) :
    (EModel q →L[ℝ] EModel q) →ₗ[ℝ] Module.End ℝ (EModel q) where
  toFun S := S.toLinearMap
  map_add' S T := by ext v; rfl
  map_smul' r S := by ext v; rfl

theorem localContinuousSpan_eq_actualPlane
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n) :
    letI := a.quotientCharts
    Submodule.map (forgetContinuousEnd q)
      (Submodule.span ℝ (Set.range
        (localQuaternionicGenerator hLee hDesc hImm n d e q g a hq hn x y))) =
      euclideanLocalFrameSpan hDesc hImm n d e q g a hq
        (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x) x y := by
  letI := a.quotientCharts
  rw [Submodule.map_span]
  unfold euclideanLocalFrameSpan
  congr 1
  ext S
  constructor
  · rintro ⟨T, ⟨t, rfl⟩, rfl⟩
    fin_cases t <;> simp [localQuaternionicGenerator, forgetContinuousEnd]
  · intro hS
    rcases Set.mem_insert_iff.mp hS with hI | hS
    · subst S
      exact ⟨_, ⟨0, rfl⟩, by simp [localQuaternionicGenerator, forgetContinuousEnd]⟩
    rcases Set.mem_insert_iff.mp hS with hJ | hS
    · subst S
      exact ⟨_, ⟨1, rfl⟩, by simp [localQuaternionicGenerator, forgetContinuousEnd]⟩
    · have hK := Set.mem_singleton_iff.mp hS
      subst S
      exact ⟨_, ⟨2, rfl⟩, by simp [localQuaternionicGenerator, forgetContinuousEnd]⟩

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameQuaternionicSpanBridge
