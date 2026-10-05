import QuaternionicSymmetry.QuaternionicManifoldFixedNormalizer
import QuaternionicSymmetry.QuaternionicLieAlgebraProjectionLaws
import QuaternionicSymmetry.QuaternionicLieAlgebraProjectionEquivariance

/-! The infinitesimal quaternionic splitting is natural under the constant
isometry identifying one adapted chart with the fixed model. -/

namespace QuaternionicSymmetry.QuaternionicManifoldModelProjection

open QuaternionicManifoldFixedNormalizer QuaternionicIsometryNormalizer
  QuaternionicLieAlgebraProjection
  VectorBundleFrameTransitions
  VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Quaternion
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
variable (S T : QuaternionicStructure E)

theorem modelGauge_symm_conjugation_synth (a : Fin 3 → ℝ) :
    conjugation (modelGauge S T).symm (synth T a) = synth S a := by
  apply (conjugation (modelGauge S T)).injective
  rw [← conjugation_mul]
  have hmul : modelGauge S T * (modelGauge S T).symm = 1 := by
    change modelGauge S T * (modelGauge S T)⁻¹ = 1
    group
  rw [hmul, conjugation_one]
  exact (modelGauge_conjugation_synth S T a).symm

theorem modelGauge_symm_conjugation_commutes
    (A : E →L[ℝ] E)
    (hA : ∀ a, A * synth T a = synth T a * A) (a : Fin 3 → ℝ) :
    conjugation (modelGauge S T).symm A * synth S a =
      synth S a * conjugation (modelGauge S T).symm A := by
  rw [← modelGauge_symm_conjugation_synth S T a]
  rw [← conjugation_product, ← conjugation_product, hA]

theorem symplecticProjection_modelGauge (A : E →L[ℝ] E)
    (hA : ∀ a, symplecticProjection T A * synth T a =
      synth T a * symplecticProjection T A) :
    symplecticProjection S (conjugation (modelGauge S T).symm A) =
      conjugation (modelGauge S T).symm (symplecticProjection T A) := by
  let C := conjugation (modelGauge S T).symm
  have hzero : scalarProjection S (C (symplecticProjection T A)) = 0 :=
    scalarProjection_eq_zero_of_commutes S _
      (modelGauge_symm_conjugation_commutes S T _ hA)
  have hscalar : scalarProjection S (C (scalarProjection T A)) =
      C (scalarProjection T A) := by
    change scalarProjection S (C (synth T _)) = C (synth T _)
    rw [modelGauge_symm_conjugation_synth, scalarProjection_synth]
  have hsplit : A = symplecticProjection T A + scalarProjection T A :=
    (projection_sum T A).symm
  change C A - scalarProjection S (C A) = C (symplecticProjection T A)
  conv_lhs => rw [hsplit]
  rw [map_add, map_add, hzero, hscalar]
  abel

end
end QuaternionicSymmetry.QuaternionicManifoldModelProjection
