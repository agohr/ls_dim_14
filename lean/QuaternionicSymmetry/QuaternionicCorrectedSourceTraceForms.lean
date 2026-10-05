import QuaternionicSymmetry.QuaternionicCorrectedMatrixTraceForms
import QuaternionicSymmetry.ComplexEvenTraceNormalization
import QuaternionicSymmetry.QuaternionicManifoldCorrectedTracePowers

/-! The paper's normalized signed even matrix traces are the actual closed
standard Chern--Weil forms, with coefficient (2π)^(-2j)/4 on real traces. -/
namespace QuaternionicSymmetry.QuaternionicCorrectedSourceTraceForms
open QuaternionicCorrectedMatrixTraceForms QuaternionicCorrectedCurvatureMatrix
open QuaternionicManifoldCorrectedConnection QuaternionicManifoldCorrectedTracePowers
open QuaternionicProjectiveStandardHilbertStructure ContinuousAlgebraWedgePowers
open ComplexEvenTraceNormalization LocalChernWeilTracePowers
open ManifoldDifferentialForms
open scoped Manifold ContDiff Matrix
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedRing (Matrix
    (Fin (standardStructure S).quaternionicDimension ⊕ Fin (standardStructure S).quaternionicDimension)
    (Fin (standardStructure S).quaternionicDimension ⊕ Fin (standardStructure S).quaternionicDimension) ℂ) :=
  Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix
    (Fin (standardStructure S).quaternionicDimension ⊕ Fin (standardStructure S).quaternionicDimension)
    (Fin (standardStructure S).quaternionicDimension ⊕ Fin (standardStructure S).quaternionicDimension) ℂ) :=
  Matrix.linftyOpNormedAlgebra
local instance : NormedAlgebra ℂ (Matrix
    (Fin (standardStructure S).quaternionicDimension ⊕ Fin (standardStructure S).quaternionicDimension)
    (Fin (standardStructure S).quaternionicDimension ⊕ Fin (standardStructure S).quaternionicDimension) ℂ) :=
  Matrix.linftyOpNormedAlgebra

def sourceMatrixForm (t : ℝ) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ) * Complex.I) • correctedMatrixForm S Q D t p y hy

theorem sourceMatrixForm_apply (t : ℝ) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v : Fin 2 → E) :
    sourceMatrixForm S Q D t p y hy v =
      sourceCurvatureMatrix S Q D t p y (v 0) (v 1) hy := by
  simp only [sourceMatrixForm, ContinuousAlternatingMap.smul_apply,
    correctedMatrixForm_apply, sourceCurvatureMatrix, mul_smul, Complex.coe_smul]

theorem signedTrace_eq_realTrace (t : ℝ) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (j : ℕ) (hj : 0 < j)
    (v : Fin (powerDegree (2 * j - 1)) → E) :
    ((-1 : ℝ) ^ j / 2) * (power (sourceMatrixForm S Q D t p y hy) (2 * j - 1) v).trace.re =
      ((1 / (2 * Real.pi)) ^ (2 * j) / 4) *
        tracePowerForm LocalEndomorphismTrace.traceCLM
          (correctedConnection S Q D t p) (2 * j - 1) y v := by
  rw [sourceMatrixForm, signed_even_trace _ _ j hj,
    tracePowerForm_eq_matrix S Q D t p y hy]
  ring

def closedSourceEvenTrace (t : ℝ) (j : ℕ) :
    closedForms (E := E) (M₀ := M) (powerDegree (2 * j - 1)) :=
  ((1 / (2 * Real.pi)) ^ (2 * j) / 4 : ℝ) • closedTracePower S Q D t (2 * j - 1)

theorem closedSourceEvenTrace_chart (t : ℝ) (j : ℕ) (hj : 0 < j)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (v : Fin (powerDegree (2 * j - 1)) → E) :
    inChartModel p (closedSourceEvenTrace S Q D t j).val.val y v =
      ((-1 : ℝ) ^ j / 2) *
        (power (sourceMatrixForm S Q D t p y hy) (2 * j - 1) v).trace.re := by
  change inChartModel p (((1 / (2 * Real.pi)) ^ (2 * j) / 4 : ℝ) •
    (traceAtlas S Q D t (2 * j - 1)).globalForm) y v = _
  rw [inChartModel_smul]
  change ((1 / (2 * Real.pi)) ^ (2 * j) / 4 : ℝ) *
    inChartModel p (traceAtlas S Q D t (2 * j - 1)).globalForm y v = _
  rw [(traceAtlas S Q D t (2 * j - 1)).globalForm_chart p hy]
  exact (signedTrace_eq_realTrace S Q D t p y hy j hj v).symm

end
end QuaternionicSymmetry.QuaternionicCorrectedSourceTraceForms
