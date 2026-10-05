import QuaternionicSymmetry.ManifoldClosedRecoveredPowers
import QuaternionicSymmetry.ManifoldClosedTangentGenerators
import QuaternionicSymmetry.QuaternionicRootRecoveryNaturality

/-! The reconstructed actual closed forms represent the previously defined
analytic tangent-root candidate classes. -/
namespace QuaternionicSymmetry.ManifoldClosedRecoveredClassComparison
open ManifoldClosedTangentGenerators ManifoldEvenClosedClassMap
open ManifoldQuaternionicAdjointChernWeil QuaternionicRootRecoveryNaturality
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : Algebra ℚ (ManifoldEvenClosedAlgebra.Total (E := E) (M := M)) :=
  ManifoldEvenClosedAlgebra.rationalConstants.toAlgebra
local instance : Algebra ℚ (ManifoldEvenCharacteristicAlgebra.Total (E := E) (M := M)) :=
  ManifoldTangentTraceRootCandidates.rationalAlgebra
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

def recoveredForm (qdim : ℕ) (j : Fin 7) : ManifoldEvenClosedAlgebra.Grade E M j.val :=
  ManifoldClosedRecoveredPowers.candidatePowerClass
    (quarterPontryaginCandidateForm Q D) (normalizedTangentGrade Q D) qdim j

theorem classMap_quarter :
    classMap (ManifoldClosedRecoveredPowers.quarterUTotal
      (quarterPontryaginCandidateForm Q D) (normalizedTangentGrade Q D)) =
      ManifoldTangentTraceRootCandidates.quarterUTotal Q D := by
  rw [ManifoldClosedRecoveredPowers.quarterUTotal, classMap_of, quarterForm_class]
  rfl

theorem classMap_tangent (qdim j : ℕ) :
    classMap (ManifoldClosedRecoveredPowers.normalizedTangentHalfTrace
      (quarterPontryaginCandidateForm Q D) (normalizedTangentGrade Q D) qdim j) =
      ManifoldTangentTraceRootCandidates.normalizedTangentHalfTrace Q D qdim j := by
  cases j with
  | zero =>
      have h : (classMap (E := E) (M := M)).comp ManifoldEvenClosedAlgebra.rationalConstants =
          ManifoldEvenCharacteristicAlgebra.rationalConstants := Subsingleton.elim _ _
      exact RingHom.congr_fun h (2*qdim)
  | succ k =>
      rw [ManifoldClosedRecoveredPowers.normalizedTangentHalfTrace, classMap_of,
        normalizedTangentGrade_class]
      rfl

theorem classMap_candidate (qdim : ℕ) (j : Fin 7) :
    classMap (ManifoldClosedRecoveredPowers.candidatePower
      (quarterPontryaginCandidateForm Q D) (normalizedTangentGrade Q D) qdim j) =
      ManifoldTangentTraceRootCandidates.candidatePower Q D qdim j := by
  unfold ManifoldClosedRecoveredPowers.candidatePower
  rw [map_recoveredStandardPower, classMap_quarter]
  simp only [classMap_tangent]
  rfl

theorem recoveredForm_class (qdim : ℕ) (j : Fin 7) :
    classGrade j.val (recoveredForm Q D qdim j) =
      ManifoldTangentTraceRootCandidates.candidatePowerClass Q D qdim j := by
  apply DirectSum.of_injective
  rw [← classMap_of]
  change classMap (DirectSum.of _ j.val (ManifoldClosedRecoveredPowers.candidatePowerClass
    (quarterPontryaginCandidateForm Q D) (normalizedTangentGrade Q D) qdim j)) = _
  rw [← ManifoldClosedRecoveredPowers.candidatePower_eq_of_class, classMap_candidate,
    ManifoldTangentTraceRootCandidates.candidatePower_eq_of_class]

end
end QuaternionicSymmetry.ManifoldClosedRecoveredClassComparison
