import QuaternionicSymmetry.QuaternionicLieAlgebraProjectionLaws

/-! Lie bracket compatibility of the scalar projection on infinitesimal
quaternionic normalizers. -/
namespace QuaternionicSymmetry.QuaternionicLieAlgebraProjection

open ManifoldQuaternionicRankThreeOrientation
  VectorBundleFrameTransitions.QuaternionicFrameReduction
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

omit [FiniteDimensional ℝ E] in
theorem commutator_commutes_synth (S : QuaternionicStructure E) (A B : E →L[ℝ] E)
    (hA : ∀ a, A * synth S a = synth S a * A)
    (hB : ∀ a, B * synth S a = synth S a * B) (a : Fin 3 → ℝ) :
    (A * B - B * A) * synth S a = synth S a * (A * B - B * A) := by
  calc
    _ = A * (B * synth S a) - B * (A * synth S a) := by noncomm_ring
    _ = A * (synth S a * B) - B * (synth S a * A) := by rw [hA a, hB a]
    _ = (A * synth S a) * B - (B * synth S a) * A := by noncomm_ring
    _ = (synth S a * A) * B - (synth S a * B) * A := by rw [hA a, hB a]
    _ = _ := by noncomm_ring

theorem scalarProjection_scalar_commutator (S : QuaternionicStructure E) (A B : E →L[ℝ] E) :
    scalarProjection S (scalarProjection S A * scalarProjection S B -
      scalarProjection S B * scalarProjection S A) =
        scalarProjection S A * scalarProjection S B - scalarProjection S B * scalarProjection S A := by
  change scalarProjection S (synth S _ * synth S _ - synth S _ * synth S _) =
    synth S _ * synth S _ - synth S _ * synth S _
  rw [synth_commutator_cross, map_smul, scalarProjection_synth]

theorem scalarProjection_commutator (S : QuaternionicStructure E) (A B : E →L[ℝ] E)
    (hA : ∀ a, symplecticProjection S A * synth S a = synth S a * symplecticProjection S A)
    (hB : ∀ a, symplecticProjection S B * synth S a = synth S a * symplecticProjection S B) :
    scalarProjection S (A * B - B * A) =
      scalarProjection S A * scalarProjection S B - scalarProjection S B * scalarProjection S A := by
  have hAB : symplecticProjection S A * scalarProjection S B =
      scalarProjection S B * symplecticProjection S A := hA _
  have hBA : symplecticProjection S B * scalarProjection S A =
      scalarProjection S A * symplecticProjection S B := hB _
  have hsplit : A * B - B * A =
      (symplecticProjection S A * symplecticProjection S B -
        symplecticProjection S B * symplecticProjection S A) +
      (scalarProjection S A * scalarProjection S B -
        scalarProjection S B * scalarProjection S A) := by
    calc
      _ = (symplecticProjection S A + scalarProjection S A) *
            (symplecticProjection S B + scalarProjection S B) -
          (symplecticProjection S B + scalarProjection S B) *
            (symplecticProjection S A + scalarProjection S A) := by
              rw [projection_sum, projection_sum]
      _ = _ := by
        simp only [add_mul, mul_add]
        rw [hAB, hBA]
        abel
  rw [hsplit, map_add, scalarProjection_eq_zero_of_commutes S _
    (commutator_commutes_synth S _ _ hA hB), zero_add,
    scalarProjection_scalar_commutator]

end
end QuaternionicSymmetry.QuaternionicLieAlgebraProjection
