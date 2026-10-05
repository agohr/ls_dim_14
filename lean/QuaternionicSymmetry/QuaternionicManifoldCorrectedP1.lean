import QuaternionicSymmetry.QuaternionicManifoldCorrectedTransgression
import QuaternionicSymmetry.ManifoldQuaternionicStandardTraceClass

/-! The normalized first trace class of the actual corrected connection
equals the recovered analytic p1 class, for every path parameter. -/
namespace QuaternionicSymmetry.QuaternionicManifoldCorrectedP1
open QuaternionicManifoldCorrectedConnection QuaternionicManifoldCorrectedTracePowers
open QuaternionicManifoldCorrectedTransgression ManifoldQuaternionicStandardTraceClass
open ManifoldDifferentialForms ManifoldDeRhamWedge ManifoldDeRhamRing
open LocalChernWeilTracePowers
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem closedTracePower_zero_one :
    closedTracePower S Q D 0 1 = closedStandardTraceSquare Q D := by
  apply Subtype.ext
  apply Subtype.ext
  apply form_ext_center
  intro x
  change inChartModel x (traceAtlas S Q D 0 1).globalForm (extChartAt 𝓘(ℝ,E) x x) = _
  rw [(traceAtlas S Q D 0 1).globalForm_chart x (mem_extChartAt_target x),
    closedStandardTraceSquare_chart S Q D x _ (mem_extChartAt_target x)]
  have h0 : correctedConnection S Q D 0 x =
      QuaternionicManifoldProjectiveStandardConnection.standardConnection S Q D x := by
    funext y
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro z
    change QuaternionicManifoldProjectiveStandardConnection.standardConnection S Q D x y u z +
      (0 : ℝ) • QuaternionicManifoldStandardSolder.standardSolder S Q x y u z = _
    rw [zero_smul, add_zero]
  change traceCurvaturePowerForm (correctedConnection S Q D 0 x) 1 _ = _
  rw [h0]
  exact congrFun (tracePowerForm_one_eq_traceSquareForm _ _) _

def correctedP1 (t : ℝ) : closedForms (E := E) (M₀ := M) 4 :=
  (1 / (16 * Real.pi ^ 2) : ℝ) • closedTracePower S Q D t 1

def correctedP1Class (t : ℝ) : positiveDegreeCohomology (E := E) (M₀ := M) 3 :=
  closedFormClassHom 3 (correctedP1 S Q D t)

theorem correctedP1Class_eq_standard (t : ℝ) :
    correctedP1Class S Q D t = standardP1Class Q D := by
  have h : closedFormClass 3 (closedTracePower S Q D t 1) =
      closedFormClass 3 (closedTracePower S Q D 0 1) :=
    closedTracePower_class_eq S Q D 0 t 1
  rw [closedTracePower_zero_one S Q D] at h
  change closedFormClass 3 ((1 / (16 * Real.pi ^ 2) : ℝ) • closedTracePower S Q D t 1) =
    closedFormClass 3 ((1 / (16 * Real.pi ^ 2) : ℝ) • closedStandardTraceSquare Q D)
  rw [closedFormClass_smul, closedFormClass_smul, h]

end
end QuaternionicSymmetry.QuaternionicManifoldCorrectedP1
