import QuaternionicSymmetry.QuaternionicMatrixTwoFormTrace
import QuaternionicSymmetry.QuaternionicCorrectedCurvatureMatrix

/-! Every actual corrected Chern--Weil trace power equals twice the real
part of the corresponding fixed complex matrix wedge trace. -/
namespace QuaternionicSymmetry.QuaternionicCorrectedMatrixTraceForms
open QuaternionicCorrectedCurvatureStructure QuaternionicCorrectedCurvatureMatrix
open QuaternionicManifoldCorrectedConnection QuaternionicProjectiveStandardL2
open QuaternionicProjectiveStandardHilbertStructure QuaternionicMatrixTwoFormTrace
open ContinuousAlgebraWedgePowers LocalChernWeilTracePowers LocalConnectionForms
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
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance
local instance : NormedRing (Matrix
    (Fin (standardStructure S).quaternionicDimension ⊕ Fin (standardStructure S).quaternionicDimension)
    (Fin (standardStructure S).quaternionicDimension ⊕ Fin (standardStructure S).quaternionicDimension) ℂ) :=
  Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix
    (Fin (standardStructure S).quaternionicDimension ⊕ Fin (standardStructure S).quaternionicDimension)
    (Fin (standardStructure S).quaternionicDimension ⊕ Fin (standardStructure S).quaternionicDimension) ℂ) :=
  Matrix.linftyOpNormedAlgebra

theorem curvatureForm_I (t : ℝ) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v : Fin 2 → E) (z : StandardSpace (E := E)) :
    curvatureForm (correctedConnection S Q D t p) y v ((standardStructure S).I z) =
      (standardStructure S).I (curvatureForm (correctedConnection S Q D t p) y v z) := by
  rw [curvatureForm_apply]
  exact curvature_I S Q D t p y (v 0) (v 1) hy z

def correctedMatrixForm (t : ℝ) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :=
  matrixForm (standardStructure S) (curvatureForm (correctedConnection S Q D t p) y)
    (curvatureForm_I S Q D t p y hy)

theorem correctedMatrixForm_apply (t : ℝ) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v : Fin 2 → E) :
    correctedMatrixForm S Q D t p y hy v = curvatureMatrix S Q D t p y (v 0) (v 1) hy := by
  change QuaternionicOperatorMatrix.operatorMatrix (standardStructure S)
      (curvatureForm (correctedConnection S Q D t p) y v).toLinearMap
      (curvatureForm_I S Q D t p y hy v) = _
  unfold curvatureMatrix
  congr 1
  exact congrArg ContinuousLinearMap.toLinearMap (curvatureForm_apply _ y v)

theorem tracePowerForm_eq_matrix (t : ℝ) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (k : ℕ) (v : Fin (powerDegree k) → E) :
    tracePowerForm LocalEndomorphismTrace.traceCLM (correctedConnection S Q D t p) k y v =
      2 * (power (correctedMatrixForm S Q D t p y hy) k v).trace.re := by
  have h := trace_power (standardStructure S)
    (curvatureForm (correctedConnection S Q D t p) y)
    (curvatureForm_I S Q D t p y hy) k v
  rw [power_curvatureForm] at h
  exact h

end
end QuaternionicSymmetry.QuaternionicCorrectedMatrixTraceForms
