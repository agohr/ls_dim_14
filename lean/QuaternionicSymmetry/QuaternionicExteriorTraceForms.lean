import QuaternionicSymmetry.EvenExteriorMatrixHomogeneity

/-! Homogeneous exterior representatives of the universal even trace powers.
The canonical exterior pairing converts these to normalized continuous
alternating forms in degree `4j`. -/
namespace QuaternionicSymmetry.QuaternionicExteriorTraceForms
open QuaternionicExteriorEvenTrace QuaternionicUniversalEvenTrace
  EvenExteriorMatrixHomogeneity EvenForms ExteriorContinuousPairing
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

private abbrev X := ExteriorAlgebra ℝ (Module.Dual ℝ V)

omit [FiniteDimensional ℝ V] in
private theorem line_entries_degree_two (ω : Fin 3 → Power V 2)
    (i j : Fin 4) :
    ((lineMatrix (liftTwo ω) i j : EvenAlgebra V) : X (V := V)) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V) := by
  fin_cases i <;> fin_cases j <;>
    simp [lineMatrix, liftTwo, ofTwoForm_coe]

omit [FiniteDimensional ℝ V] in
private theorem adjoint_entries_degree_two (ω : Fin 3 → Power V 2)
    (i j : Fin 3) :
    ((adjointMatrix (liftTwo ω) i j : EvenAlgebra V) : X (V := V)) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V) := by
  have htwo (k : Fin 3) :
      (2 : X (V := V)) * (ω k).val ∈
        ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V) := by
    have h := (ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V)).smul_mem
      (2 : ℝ) (ω k).property
    simpa only [Algebra.smul_def, map_ofNat] using h
  fin_cases i <;> fin_cases j <;>
    simp [adjointMatrix, liftTwo, ofTwoForm_coe]
  all_goals first | exact htwo 0 | exact htwo 1 | exact htwo 2

/-- Exterior representative of the quaternionic-line trace of `F^(2j)`. -/
def lineTracePower (ω : Fin 3 → Power V 2) (j : ℕ) : Power V (4 * j) :=
  ⟨(Matrix.trace (lineMatrix (liftTwo ω) ^ (2 * j)) : EvenAlgebra V), by
    rw [show 4 * j = 2 * (2 * j) by omega]
    exact matrix_trace_pow_mem 2 (2 * j) (lineMatrix (liftTwo ω))
      (line_entries_degree_two ω)⟩

/-- Exterior representative of the induced rank-three trace of `F^(2j)`. -/
def adjointTracePower (ω : Fin 3 → Power V 2) (j : ℕ) : Power V (4 * j) :=
  ⟨(Matrix.trace (adjointMatrix (liftTwo ω) ^ (2 * j)) : EvenAlgebra V), by
    rw [show 4 * j = 2 * (2 * j) by omega]
    exact matrix_trace_pow_mem 2 (2 * j) (adjointMatrix (liftTwo ω))
      (adjoint_entries_degree_two ω)⟩

omit [FiniteDimensional ℝ V] in
/-- Exact ratio as an equality of actual homogeneous exterior forms. -/
theorem line_adjoint_tracePower (ω : Fin 3 → Power V 2)
    (j : ℕ) (hj : 0 < j) :
    (4 : ℝ) ^ j • lineTracePower ω j =
      (2 : ℝ) • adjointTracePower ω j := by
  apply Subtype.ext
  change ((4 : ℝ) ^ j) •
      ((Matrix.trace (lineMatrix (liftTwo ω) ^ (2 * j)) : EvenAlgebra V) : X (V := V)) =
    2 • ((Matrix.trace (adjointMatrix (liftTwo ω) ^ (2 * j)) : EvenAlgebra V) : X (V := V))
  simpa [Algebra.smul_def] using congrArg
    (fun z : EvenAlgebra V => (z : X (V := V)))
      (exterior_line_adjoint_even_trace ω j hj)

/-- The same identity after the canonical pairing with vectors, with the
normalized wedge convention fixed by `ExteriorContinuousWedge`. -/
theorem line_adjoint_continuousTracePower (ω : Fin 3 → Power V 2)
    (j : ℕ) (hj : 0 < j) :
    (4 : ℝ) ^ j • toContinuous (4 * j) (lineTracePower ω j) =
      (2 : ℝ) • toContinuous (4 * j) (adjointTracePower ω j) := by
  simpa only [toContinuous_smul] using
    congrArg (toContinuous (V := V) (4 * j))
      (line_adjoint_tracePower ω j hj)

end
end QuaternionicSymmetry.QuaternionicExteriorTraceForms
