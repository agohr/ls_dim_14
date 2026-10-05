import QuaternionicSymmetry.QuaternionicCorrectedSourceTraceForms
import QuaternionicSymmetry.ManifoldSevenVariableClosedEvaluation
import QuaternionicSymmetry.ManifoldQuaternionicAdjointChernWeil
import QuaternionicSymmetry.ManifoldDeRhamAllDegrees

/-! Genuine globally closed characteristic generators for the corrected
standard connection, in the exact degree convention of the density polynomials. -/
namespace QuaternionicSymmetry.QuaternionicClosedSourceGenerators
open QuaternionicCorrectedSourceTraceForms ManifoldDifferentialForms
open LocalChernWeilTracePowers ManifoldDeRhamAllDegrees
open ManifoldQuaternionicAdjointChernWeil
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem sourceDegree (k : ℕ) : powerDegree (2*(k+1)-1) = 4*k+3+1 := by
  rw [powerDegree_eq]
  omega

def sourceGrade (t : ℝ) (k : ℕ) : ManifoldEvenClosedAlgebra.Grade E M (k+1) :=
  castClosedDegree (sourceDegree k) (closedSourceEvenTrace S Q D t (k+1))

def generators (t : ℝ) :
    ManifoldSevenVariableClosedEvaluation.Generators (E := E) (M := M) where
  u := quarterPontryaginCandidateForm Q D
  p1 := sourceGrade S Q D t 0
  p2 := sourceGrade S Q D t 1
  p3 := sourceGrade S Q D t 2
  p4 := sourceGrade S Q D t 3
  p5 := sourceGrade S Q D t 4
  p6 := sourceGrade S Q D t 5

end
end QuaternionicSymmetry.QuaternionicClosedSourceGenerators
