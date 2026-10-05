import QuaternionicSymmetry.CompactSymplecticStabilizerProductTopology
import QuaternionicSymmetry.ManifoldDimensionTopologySource
import QuaternionicSymmetry.CompactSymplecticMatrixUnits

/-! Transfer of Lie-atlas dimension across the checked homeomorphism
`K ≃ₜ Sp(1) × Sp(n)`. The only background input is general Brouwer
invariance of dimension; no stabilizer-specific dimension is premised. -/

namespace QuaternionicSymmetry.CompactSymplecticStabilizerDimensionTransfer

open Manifold CompactSymplecticProjectiveQuotient
open CompactSymplecticStabilizerProductTopology
open GeneralRealProductManifold ManifoldDimensionTopologySource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev K (n : ℕ) := firstPairStabilizer n
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev Mat (n : ℕ) :=
  Matrix (Fin (n + 1) ⊕ Fin (n + 1))
    (Fin (n + 1) ⊕ Fin (n + 1)) ℂ

/-- For `n=m+1` the two factors are both in the `Group (k+1)` family
supplied with genuine Lee or Knapp atlases. -/
theorem stabilizer_model_dimension_eq_sum
    (hDim : LeeInvarianceOfDimension)
    (m e d₁ d₂ : ℕ)
    (kCharts : ChartedSpace (RModel e) (K (m + 1)))
    (hk : letI := kCharts; IsManifold 𝓘(ℝ, RModel e) ∞ (K (m + 1)))
    (a₁ : ChartedSpace (RModel d₁) (G 0))
    (ha₁ : letI := a₁; IsManifold 𝓘(ℝ, RModel d₁) ∞ (G 0))
    (a₂ : ChartedSpace (RModel d₂) (G m))
    (ha₂ : letI := a₂; IsManifold 𝓘(ℝ, RModel d₂) ∞ (G m)) :
    e = d₁ + d₂ := by
  letI : ChartedSpace (RModel e) (K (m + 1)) := kCharts
  letI : IsManifold 𝓘(ℝ, RModel e) ∞ (K (m + 1)) := hk
  letI : ChartedSpace (RModel d₁) (G 0) := a₁
  letI : ChartedSpace (RModel d₂) (G m) := a₂
  letI : IsManifold 𝓘(ℝ, RModel d₁) ∞ (G 0) := ha₁
  letI : IsManifold 𝓘(ℝ, RModel d₂) ∞ (G m) := ha₂
  obtain ⟨prodCharts, prodManifold⟩ :=
    exists_product_atlas d₁ d₂ a₁ a₂ ha₁ ha₂
  letI : ChartedSpace (ModelProd (RModel d₁) (RModel d₂)) (G 0 × G m) := prodCharts
  letI : IsManifold 𝓘(ℝ, ModelProd (RModel d₁) (RModel d₂)) ∞
      (G 0 × G m) := prodManifold
  letI : NormedAddCommGroup (ModelProd (RModel d₁) (RModel d₂)) :=
    inferInstanceAs (NormedAddCommGroup (RModel d₁ × RModel d₂))
  letI : NormedSpace ℝ (ModelProd (RModel d₁) (RModel d₂)) :=
    inferInstanceAs (NormedSpace ℝ (RModel d₁ × RModel d₂))
  letI : FiniteDimensional ℝ (ModelProd (RModel d₁) (RModel d₂)) :=
    inferInstanceAs (FiniteDimensional ℝ (RModel d₁ × RModel d₂))
  letI : SecondCountableTopology (Mat 0)ˣ :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (Mat m)ˣ :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (Mat (m + 1))ˣ :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (G 0) :=
    (CompactSymplecticMatrixUnits.toMatrixUnits_closedEmbedding 0).isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (G m) :=
    (CompactSymplecticMatrixUnits.toMatrixUnits_closedEmbedding m).isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (G (m + 1)) :=
    (CompactSymplecticMatrixUnits.toMatrixUnits_closedEmbedding (m + 1)).isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (K (m + 1)) :=
    (isClosed_firstPairStabilizer (m + 1)).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  letI : Nonempty (K (m + 1)) := ⟨1⟩
  have h := hDim (E := RModel e)
    (F := ModelProd (RModel d₁) (RModel d₂))
    (X := K (m + 1)) (Y := G 0 × G m)
    (stabilizerProductHomeomorph (m + 1))
  simpa [Module.finrank_fin_fun, finrank_product_model] using h

end
end QuaternionicSymmetry.CompactSymplecticStabilizerDimensionTransfer
