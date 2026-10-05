import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanQuaternionicMetric

/-! A genuine Euclidean-valued chart atlas for the selected projector quotient. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorEuclideanCharts

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

def euclideanCoordinateCharts (q : ℕ) : ChartedSpace (EModel q) (RModel q) :=
  ((euclideanModelEquiv q).toHomeomorph.toOpenPartialHomeomorph).singletonChartedSpace
    (by simp)

theorem euclideanCoordinateCharts_isManifold (q : ℕ) :
    letI := euclideanCoordinateCharts q
    IsManifold 𝓘(ℝ, EModel q) ∞ (RModel q) := by
  let e := (euclideanModelEquiv q).toHomeomorph.toOpenPartialHomeomorph
  have he : e.source = Set.univ := by simp [e]
  change @IsManifold ℝ _ (EModel q) _ _ (EModel q) _ 𝓘(ℝ, EModel q) ∞
    (RModel q) _ (e.singletonChartedSpace he)
  exact e.isManifold_singleton he

def euclideanQuotientCharts
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    ChartedSpace (EModel q) (ProjectiveCarrier n) := by
  letI := a.quotientCharts
  letI := euclideanCoordinateCharts q
  exact ChartedSpace.comp (EModel q) (RModel q) (ProjectiveCarrier n)

theorem euclideanQuotientCharts_chartAt
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := euclideanQuotientCharts n d e q g a
    chartAt (EModel q) x =
      (letI := a.quotientCharts
       (chartAt (RModel q) x).trans
         ((euclideanModelEquiv q).toHomeomorph.toOpenPartialHomeomorph)) := by
  rfl

theorem euclideanQuotientCharts_isManifold
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := euclideanQuotientCharts n d e q g a
    IsManifold 𝓘(ℝ, EModel q) ∞ (ProjectiveCarrier n) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := euclideanCoordinateCharts q
  letI := euclideanQuotientCharts n d e q g a
  refine isManifold_of_contDiffOn 𝓘(ℝ, EModel q) ∞ (ProjectiveCarrier n) ?_
  intro c c' hc hc'
  rcases hc with ⟨e₁, he₁, f₁, hf₁, rfl⟩
  rcases hc' with ⟨e₂, he₂, f₂, hf₂, rfl⟩
  change f₁ = (euclideanModelEquiv q).toHomeomorph.toOpenPartialHomeomorph at hf₁
  change f₂ = (euclideanModelEquiv q).toHomeomorph.toOpenPartialHomeomorph at hf₂
  subst f₁
  subst f₂
  let L := euclideanModelEquiv q
  have hOld := ((contDiffGroupoid ∞ 𝓘(ℝ, RModel q)).compatible he₁ he₂).1
  have hNew : ContDiffOn ℝ ∞ (L ∘ (e₁.symm ≫ₕ e₂) ∘ L.symm)
      (L.symm ⁻¹' (e₁.symm ≫ₕ e₂).source) := by
    refine L.contDiff.comp_contDiffOn (hOld.comp L.symm.contDiff.contDiffOn ?_)
    intro x hx
    simpa [mfld_simps] using hx
  convert hNew using 1
  simp [L, mfld_simps, Function.comp_def]
  ext x
  rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorEuclideanCharts
