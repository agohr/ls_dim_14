import QuaternionicSymmetry.QuaternionicLieAlgebraProjectionLaws
import QuaternionicSymmetry.QuaternionicIsometryNormalizer

/-! Invariance of the infinitesimal splitting under the quaternionic
isometry normalizer. -/
namespace QuaternionicSymmetry.QuaternionicLieAlgebraProjection

open QuaternionicIsometryNormalizer
  VectorBundleFrameTransitions.QuaternionicFrameReduction
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem conjugation_product (g : E ≃ₗᵢ[ℝ] E) (A B : E →L[ℝ] E) :
    conjugation g (A * B) = conjugation g A * conjugation g B :=
  (g.toContinuousLinearEquiv.conjContinuousAlgEquiv).map_mul A B

variable [FiniteDimensional ℝ E] [Nontrivial E]

theorem conjugation_commutes_synth (S : QuaternionicStructure E) (g : normalizer S)
    (A : E →L[ℝ] E) (hA : ∀ a, A * synth S a = synth S a * A) (b : Fin 3 → ℝ) :
    conjugation g.1 A * synth S b = synth S b * conjugation g.1 A := by
  obtain ⟨a, ha⟩ := (rotationEquiv S g).surjective b
  have hb : synth S b = conjugation g.1 (synth S a) := by
    rw [← ha]
    exact synth_rotationLinear S g a
  rw [hb, ← conjugation_product, ← conjugation_product, hA]

theorem scalarProjection_conjugation_scalar (S : QuaternionicStructure E)
    (g : normalizer S) (A : E →L[ℝ] E) :
    scalarProjection S (conjugation g.1 (scalarProjection S A)) =
      conjugation g.1 (scalarProjection S A) := by
  change scalarProjection S (conjugation g.1 (synth S _)) = conjugation g.1 (synth S _)
  rw [← synth_rotationLinear, scalarProjection_synth]

theorem scalarProjection_conjugation (S : QuaternionicStructure E) (g : normalizer S)
    (A : E →L[ℝ] E)
    (hA : ∀ a, symplecticProjection S A * synth S a = synth S a * symplecticProjection S A) :
    scalarProjection S (conjugation g.1 A) = conjugation g.1 (scalarProjection S A) := by
  calc
    _ = scalarProjection S (conjugation g.1
        (symplecticProjection S A + scalarProjection S A)) := by rw [projection_sum]
    _ = scalarProjection S (conjugation g.1 (symplecticProjection S A)) +
        scalarProjection S (conjugation g.1 (scalarProjection S A)) := by rw [map_add, map_add]
    _ = _ := by
      rw [scalarProjection_eq_zero_of_commutes S _
        (conjugation_commutes_synth S g _ hA), scalarProjection_conjugation_scalar, zero_add]

theorem symplecticProjection_conjugation (S : QuaternionicStructure E) (g : normalizer S)
    (A : E →L[ℝ] E)
    (hA : ∀ a, symplecticProjection S A * synth S a = synth S a * symplecticProjection S A) :
    symplecticProjection S (conjugation g.1 A) = conjugation g.1 (symplecticProjection S A) := by
  change conjugation g.1 A - scalarProjection S (conjugation g.1 A) =
    conjugation g.1 (A - scalarProjection S A)
  rw [scalarProjection_conjugation S g A hA, map_sub]

end
end QuaternionicSymmetry.QuaternionicLieAlgebraProjection
