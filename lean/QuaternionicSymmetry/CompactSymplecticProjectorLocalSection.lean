import QuaternionicSymmetry.GeneralSmoothLocalSectionSource
import QuaternionicSymmetry.CompactSymplecticProjectorTranslationDiffeomorph

/-! Apply Lee's narrow general local-section theorem to the already
proved actual smooth submersion Sp(n+1)→Sp(n+1)/K. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorLocalSection

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev Mat (n : ℕ) :=
  Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℂ

/-- A smooth local choice of genuine compact-symplectic representatives,
through any prescribed representative `u`, of the actual quotient map. -/
theorem quotient_local_section
    (hLee : LeeLocalSectionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g)
    (u : G n) :
    letI := g.charts
    letI := atlas.quotientCharts
    ∃ U : Set (ProjectiveCarrier n), IsOpen U ∧ (u : ProjectiveCarrier n) ∈ U ∧
      ∃ σ : ProjectiveCarrier n → G n,
        ContMDiffOn 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel d) ∞ σ U ∧
        σ (u : ProjectiveCarrier n) = u ∧
        ∀ x ∈ U, ((σ x : G n) : ProjectiveCarrier n) = x := by
  letI := g.charts
  letI := g.manifold
  letI := atlas.quotientCharts
  letI := atlas.quotientManifold
  letI : SecondCountableTopology (Mat n)ˣ :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (G n) :=
    (CompactSymplecticMatrixUnits.toMatrixUnits_closedEmbedding n).isEmbedding.secondCountableTopology
  exact hLee d q (fun v : G n => (v : ProjectiveCarrier n))
    atlas.quotientSmooth atlas.quotientSubmersive u

end
end QuaternionicSymmetry.CompactSymplecticProjectorLocalSection
