import QuaternionicSymmetry.ManifoldClosedRecoveredClassComparison
import QuaternionicSymmetry.ManifoldEvenClosedEvaluation

/-! Pointwise exterior evaluation of the actual closed recovered forms. -/
namespace QuaternionicSymmetry.ManifoldClosedRecoveredPointwise
open ManifoldClosedRecoveredClassComparison ManifoldClosedTangentGenerators
open ManifoldClosedRecoveredPowers ManifoldEvenClosedEvaluation
open QuaternionicRootRecoveryNaturality QuaternionicTangentRootConversion
open ManifoldQuaternionicAdjointChernWeil
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : Algebra ℚ (ManifoldEvenClosedAlgebra.Total (E := E) (M := M)) :=
  ManifoldEvenClosedAlgebra.rationalConstants.toAlgebra
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

def tangentValues (p : M) (y : E) (L : E →L[ℝ] E) (qdim : ℕ) :
    ℕ → FiberAlgebra (E := E)
  | 0 => (2 * qdim : ℕ)
  | k+1 => gradeValue p y L (k+1) (normalizedTangentGrade Q D k)

theorem evaluate_tangent (p : M) (y : E) (L : E →L[ℝ] E) (qdim j : ℕ) :
    evaluate p y L (normalizedTangentHalfTrace
      (quarterPontryaginCandidateForm Q D) (normalizedTangentGrade Q D) qdim j) =
      tangentValues Q D p y L qdim j := by
  cases j with
  | zero =>
      change evaluate p y L (ManifoldEvenClosedAlgebra.rationalConstants (2*qdim)) =
        (2*qdim : ℕ)
      simp only [map_mul, map_ofNat, map_natCast, Nat.cast_mul, Nat.cast_ofNat]
  | succ k => exact evaluate_of p y L (k+1) _

theorem recoveredForm_value (p : M) (y : E) (L : E →L[ℝ] E)
    (qdim : ℕ) (j : Fin 7) :
    gradeValue p y L j.val (recoveredForm Q D qdim j) =
      recoveredStandardPower qdim
        (gradeValue p y L 1 (quarterPontryaginCandidateForm Q D))
        (tangentValues Q D p y L qdim) j := by
  rw [← evaluate_of]
  change evaluate p y L (DirectSum.of _ j.val (candidatePowerClass
    (quarterPontryaginCandidateForm Q D) (normalizedTangentGrade Q D) qdim j)) = _
  rw [← candidatePower_eq_of_class, candidatePower, map_recoveredStandardPower,
    quarterUTotal, evaluate_of]
  have ht : (fun k => evaluate p y L (normalizedTangentHalfTrace
      (quarterPontryaginCandidateForm Q D) (normalizedTangentGrade Q D) qdim k)) =
      tangentValues Q D p y L qdim := by
    funext k
    exact evaluate_tangent Q D p y L qdim k
  rw [ht]

end
end QuaternionicSymmetry.ManifoldClosedRecoveredPointwise
