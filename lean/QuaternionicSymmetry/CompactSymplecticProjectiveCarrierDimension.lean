import QuaternionicSymmetry.CompactSymplecticKnappDimensionSource
import QuaternionicSymmetry.CompactSymplecticHomogeneousAtlasSource

/-! Real dimension of the actual coset carrier from three source-faithful
general inputs: Lee's closed-subgroup/quotient atlases (already carried by
`SmoothHomogeneousAtlas`), Lee invariance of dimension, and Knapp's
dimension of actual compact symplectic matrix groups. The stabilizer
factorization and topological equivalence are internal Lean proofs. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectiveCarrierDimension

open Manifold CompactSymplecticHaar
open CompactSymplecticProjectiveQuotient
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticStabilizerDimensionTransfer
open CompactSymplecticKnappDimensionSource
open ManifoldDimensionTopologySource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev Mat (n : ℕ) :=
  Matrix (Fin (n + 1) ⊕ Fin (n + 1))
    (Fin (n + 1) ⊕ Fin (n + 1)) ℂ

/-- The chosen smooth quotient atlas on the actual coset space has real
dimension `4n` for `n=m+1`. This does not assert a metric or an HP^n
identification. -/
theorem actual_projective_carrier_real_dimension
    (hKnapp : KnappCompactSymplecticMatrixDimension)
    (hDim : LeeInvarianceOfDimension)
    (m d e q : ℕ)
    (g : EmbeddedRealLieAtlas (m + 1) d)
    (a : SmoothHomogeneousAtlas (m + 1) d e q g) :
    q = 4 * (m + 1) := by
  obtain ⟨k₁⟩ := hKnapp 1 (by omega)
  obtain ⟨k₂⟩ := hKnapp (m + 1) (by omega)
  obtain ⟨kG⟩ := hKnapp (m + 2) (by omega)
  have he : e = 3 + (m + 1) * (2 * (m + 1) + 1) := by
    have h := stabilizer_model_dimension_eq_sum hDim m e 3
      ((m + 1) * (2 * (m + 1) + 1))
      a.stabilizerCharts a.stabilizerManifold
      k₁.charts k₁.manifold k₂.charts k₂.manifold
    simpa using h
  have hd : d = (m + 2) * (2 * (m + 2) + 1) := by
    letI : ChartedSpace (RModel d) (G (m + 1)) := g.charts
    letI : IsManifold 𝓘(ℝ, RModel d) ∞ (G (m + 1)) := g.manifold
    letI : ChartedSpace (RModel ((m + 2) * (2 * (m + 2) + 1)))
        (G (m + 1)) := kG.charts
    letI : IsManifold 𝓘(ℝ, RModel ((m + 2) * (2 * (m + 2) + 1))) ∞
        (G (m + 1)) := kG.manifold
    letI : SecondCountableTopology (Mat (m + 1))ˣ :=
      Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
    letI : SecondCountableTopology (G (m + 1)) :=
      (CompactSymplecticMatrixUnits.toMatrixUnits_closedEmbedding (m + 1)).isEmbedding.secondCountableTopology
    letI : Nonempty (G (m + 1)) := ⟨1⟩
    have h := hDim (E := RModel d)
      (F := RModel ((m + 2) * (2 * (m + 2) + 1)))
      (X := G (m + 1)) (Y := G (m + 1))
      (Homeomorph.refl (G (m + 1)))
    simpa using h
  have hq := a.dimension
  nlinarith

end
end QuaternionicSymmetry.CompactSymplecticProjectiveCarrierDimension
