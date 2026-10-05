import QuaternionicSymmetry.QuaternionicAdjointTracePowerForm
import QuaternionicSymmetry.QuaternionicScalarLineExteriorCurvature

/-! Exact scalar-line and rank-three trace ratio in the exterior algebra
of the actual axial curvature two-forms. -/
namespace QuaternionicSymmetry.QuaternionicActualExteriorTraceRatio
open QuaternionicCurvatureExteriorCoordinates QuaternionicExteriorTraceForms
  QuaternionicExteriorEvenTrace QuaternionicUniversalEvenTrace
  ExteriorMatrixTraceBridge ExteriorMatrixWedgeBridge
  ExteriorContinuousPairing ManifoldQuaternionicAdjointConnection
open scoped ContDiff Manifold
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private def axialForms (p : M) (y : E) : Fin 3 → Power E 2 :=
  fun i => axialCurvaturePower Q D p y i

/-- The scalar-line even trace and induced rank-three even trace have the
exact ratio in the actual tangent exterior algebra, at every positive power. -/
theorem scalar_adjoint_wedgeTrace_ratio (p : M) (y : E)
    (j : ℕ) (hj : 0 < j) :
    (4 : ℝ) ^ j •
      wedgeTrace (lineMatrix (liftTwo (axialForms Q D p y)))
        (QuaternionicScalarLineExteriorCurvature.line_entries_two
          (axialForms Q D p y)) (2 * j - 1) =
    (2 : ℝ) •
      wedgeTrace (adjointMatrix (liftTwo (axialForms Q D p y)))
        (QuaternionicAdjointExteriorCurvature.adjoint_entries_two
          (axialForms Q D p y)) (2 * j - 1) := by
  apply Subtype.ext
  change ((4 : ℝ) ^ j) •
      ((Matrix.trace (lineMatrix (liftTwo (axialForms Q D p y)) ^
        (2 * j - 1 + 1)) : EvenAlgebra E) :
        ExteriorAlgebra ℝ (Module.Dual ℝ E)) =
    2 • ((Matrix.trace (adjointMatrix (liftTwo (axialForms Q D p y)) ^
        (2 * j - 1 + 1)) : EvenAlgebra E) :
        ExteriorAlgebra ℝ (Module.Dual ℝ E))
  rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * j)]
  simpa [Algebra.smul_def, map_mul] using congrArg
    (fun z : EvenAlgebra E =>
      (z : ExteriorAlgebra ℝ (Module.Dual ℝ E)))
    (exterior_line_adjoint_even_trace (axialForms Q D p y) j hj)

/-- After the canonical exterior pairing, the universal scalar-line trace is
fixed by the actual induced rank-three curvature trace form. -/
theorem scalar_exterior_eq_induced_tracePowerForm (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (j : ℕ) (hj : 0 < j) :
    (4 : ℝ) ^ j •
      toContinuous (wedgeDegree (2 * j - 1))
        (wedgeTrace (lineMatrix (liftTwo (axialForms Q D p y)))
          (QuaternionicScalarLineExteriorCurvature.line_entries_two
            (axialForms Q D p y)) (2 * j - 1)) =
    (2 : ℝ) • LocalChernWeilTracePowers.tracePowerForm
      LocalEndomorphismTrace.traceCLM
      (ManifoldQuaternionicAdjointConnection.inducedForm Q D p)
      (2 * j - 1) y := by
  have h := congrArg (toContinuous (V := E) (wedgeDegree (2 * j - 1)))
    (scalar_adjoint_wedgeTrace_ratio Q D p y j hj)
  simp only [toContinuous_smul] at h
  rw [QuaternionicAdjointTracePowerForm.induced_tracePowerForm_eq_exterior
    Q D p y hy (2 * j - 1)]
  exact h

end
end QuaternionicSymmetry.QuaternionicActualExteriorTraceRatio
