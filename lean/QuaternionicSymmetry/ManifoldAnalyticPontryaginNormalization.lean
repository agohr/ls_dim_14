import QuaternionicSymmetry.ManifoldClosedTangentGenerators
import QuaternionicSymmetry.ManifoldQuaternionicAdjointChernWeilIndependence

/-! Exact Chern--Weil normalization on the actual rank-three bundle. The
result is an analytic de Rham class; identifying it with the integral
topological first Pontryagin class is a separate theorem. -/
namespace QuaternionicSymmetry.ManifoldAnalyticPontryaginNormalization
open ManifoldQuaternionicAdjointChernWeil
  ManifoldQuaternionicAdjointChernWeilIndependence
  ManifoldClosedTangentGenerators ManifoldEvenClosedClassMap
  ManifoldDifferentialForms ManifoldDeRhamRing ManifoldDeRhamWedge
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

/-- The real Chern--Weil representative in the usual trace normalization
for the first Pontryagin class of an oriented real rank-three bundle. -/
def adjointPontryaginForm : closedForms (E := E) (M₀ := M) 4 :=
  (-(1 / (8 * Real.pi ^ 2)) : ℝ) • closedTraceCurvatureSquare Q D

def adjointPontryaginClass : positiveDegreeCohomology (E := E) (M₀ := M) 3 :=
  closedFormClassHom 3 (adjointPontryaginForm Q D)

theorem adjointPontryaginForm_eq_four_quarters :
    adjointPontryaginForm Q D =
      (4 : ℝ) • quarterPontryaginCandidateForm Q D := by
  unfold adjointPontryaginForm quarterPontryaginCandidateForm
  rw [smul_smul]
  congr 1
  ring

theorem adjointPontryaginClass_eq_four_quarters :
    adjointPontryaginClass Q D =
      (4 : ℝ) • quarterPontryaginCandidateClass Q D := by
  unfold adjointPontryaginClass
  change closedFormClass 3 (adjointPontryaginForm Q D) = _
  rw [adjointPontryaginForm_eq_four_quarters, closedFormClass_smul]
  rfl

theorem adjointPontryaginClass_connection_independent
    (D' : ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    adjointPontryaginClass Q D' = adjointPontryaginClass Q D := by
  rw [adjointPontryaginClass_eq_four_quarters,
    adjointPontryaginClass_eq_four_quarters,
    quarterPontryaginCandidateClass_eq Q D D']

theorem quarterUClass_eq_quarter_adjoint :
    ManifoldTangentTraceRootCandidates.quarterUClass Q D =
      (1 / 4 : ℝ) • classGrade 1 (adjointPontryaginForm Q D) := by
  rw [adjointPontryaginForm_eq_four_quarters, map_smul]
  rw [quarterForm_class]
  simp only [smul_smul]
  norm_num

end
end QuaternionicSymmetry.ManifoldAnalyticPontryaginNormalization
