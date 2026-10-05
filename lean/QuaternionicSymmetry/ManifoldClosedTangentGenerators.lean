import QuaternionicSymmetry.ManifoldTangentTraceRootCandidates
import QuaternionicSymmetry.ManifoldEvenClosedClassMap
import QuaternionicSymmetry.ManifoldDeRhamAllDegrees

/-! Actual closed normalized tangent trace generators, with exact agreement
with the existing analytic de Rham input classes. -/
namespace QuaternionicSymmetry.ManifoldClosedTangentGenerators
open ManifoldDifferentialForms ManifoldDeRhamWedge ManifoldDeRhamRing
open ManifoldEvenClosedClassMap ManifoldQuaternionicChernWeil
open LocalChernWeilOrderedTransgression LocalChernWeilTracePowers
open ManifoldSixVariableDensityEvaluation ManifoldTangentTraceRootCandidates
open ManifoldQuaternionicAdjointChernWeil
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem tangentDegree (k : ℕ) : primitiveDegree (2*k+1) = 4*k+3 := by
  have h := primitiveDegree_add_one (2*k+1)
  rw [powerDegree_eq] at h
  omega

def rawTangentGrade (k : ℕ) : ManifoldEvenClosedAlgebra.Grade E M (k+1) :=
  ((-1 : ℝ)^(k+1)/2) • castClosed (tangentDegree k)
    ((primitiveDegree_add_one (2*k+1)).symm ▸
      (ManifoldQuaternionicChernWeil.gaugeAtlas Q D (2*k+1)).toTracePowerAtlas.closedGlobalForm)

def normalizedTangentGrade (k : ℕ) : ManifoldEvenClosedAlgebra.Grade E M (k+1) :=
  tangentTraceScale (k+1) • rawTangentGrade Q D k

omit [Nontrivial E] in
theorem rawTangentGrade_class (k : ℕ) :
    classGrade (k+1) (rawTangentGrade Q D k) = rawPowerSum Q D k := by
  rw [rawTangentGrade, map_smul]
  change ((-1:ℝ)^(k+1)/2) • closedFormClass _ (castClosed _ _) = _
  unfold rawPowerSum
  dsimp only [id_eq, ManifoldCharacteristicExpression.tangentTraceClass]
  rw [castClass_mk]
  rfl

omit [Nontrivial E] in
theorem normalizedTangentGrade_class (k : ℕ) :
    classGrade (k+1) (normalizedTangentGrade Q D k) =
      tangentTraceScale (k+1) • rawPowerSum Q D k := by
  rw [normalizedTangentGrade, map_smul, rawTangentGrade_class]

theorem quarterForm_class :
    classGrade 1 (quarterPontryaginCandidateForm Q D) = quarterUClass Q D := by
  unfold quarterPontryaginCandidateForm quarterUClass
  rw [map_smul]
  simp only [ManifoldSixVariableScaledDensity.quarterPontryaginTraceScale, neg_div]
  rfl

end
end QuaternionicSymmetry.ManifoldClosedTangentGenerators
