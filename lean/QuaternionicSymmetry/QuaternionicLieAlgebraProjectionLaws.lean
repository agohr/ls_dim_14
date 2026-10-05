import QuaternionicSymmetry.QuaternionicLieAlgebraProjection

/-! The scalar and quaternion-linear operators are complementary projections. -/
namespace QuaternionicSymmetry.QuaternionicLieAlgebraProjection

open ManifoldQuaternionicAdjointConnection ManifoldQuaternionicRankThreeOrientation
  VectorBundleFrameTransitions.QuaternionicFrameReduction
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem adjointRepresentation_synth (S : QuaternionicStructure E)
    (a b : Fin 3 → ℝ) :
    adjointRepresentation S (synth S a) b = (2 : ℝ) • crossProduct a b := by
  change coeff S (synth S a * synth S b - synth S b * synth S a) = _
  rw [synth_commutator_cross, map_smul, coeff_synth]

@[simp] theorem scalarProjection_synth (S : QuaternionicStructure E) (a : Fin 3 → ℝ) :
    scalarProjection S (synth S a) = synth S a := by
  change synth S (axialProjection (adjointRepresentation S (synth S a))) = synth S a
  congr 1
  ext i
  fin_cases i <;>
    simp [axialProjection, axialLinear, adjointRepresentation_synth,
      crossProduct, Pi.basisFun_apply]

theorem adjointRepresentation_eq_zero_of_commutes (S : QuaternionicStructure E)
    (A : E →L[ℝ] E) (hA : ∀ a, A * synth S a = synth S a * A) :
    adjointRepresentation S A = 0 := by
  ext a i
  change coeff S (A * synth S a - synth S a * A) i = 0
  rw [hA a, sub_self, map_zero]
  rfl

theorem scalarProjection_eq_zero_of_commutes (S : QuaternionicStructure E)
    (A : E →L[ℝ] E) (hA : ∀ a, A * synth S a = synth S a * A) :
    scalarProjection S A = 0 := by
  have hz := adjointRepresentation_eq_zero_of_commutes S A hA
  simp [scalarProjection, hz]

@[simp] theorem scalarProjection_idempotent (S : QuaternionicStructure E) (A : E →L[ℝ] E) :
    scalarProjection S (scalarProjection S A) = scalarProjection S A := by
  change scalarProjection S (synth S _) = synth S _
  exact scalarProjection_synth S _

@[simp] theorem scalarProjection_symplecticProjection
    (S : QuaternionicStructure E) (A : E →L[ℝ] E) :
    scalarProjection S (symplecticProjection S A) = 0 := by
  change scalarProjection S (A - scalarProjection S A) = 0
  rw [map_sub, scalarProjection_idempotent, sub_self]

@[simp] theorem symplecticProjection_scalarProjection
    (S : QuaternionicStructure E) (A : E →L[ℝ] E) :
    symplecticProjection S (scalarProjection S A) = 0 := by
  change scalarProjection S A - scalarProjection S (scalarProjection S A) = 0
  rw [scalarProjection_idempotent, sub_self]

@[simp] theorem symplecticProjection_idempotent
    (S : QuaternionicStructure E) (A : E →L[ℝ] E) :
    symplecticProjection S (symplecticProjection S A) = symplecticProjection S A := by
  change symplecticProjection S A - scalarProjection S (symplecticProjection S A) = _
  rw [scalarProjection_symplecticProjection, sub_zero]

end
end QuaternionicSymmetry.QuaternionicLieAlgebraProjection
