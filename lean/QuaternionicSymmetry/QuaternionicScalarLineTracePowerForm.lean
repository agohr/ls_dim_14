import QuaternionicSymmetry.QuaternionicScalarLineNormedCurvature
import QuaternionicSymmetry.ContinuousAlgebraWedgePowers
import QuaternionicSymmetry.ContinuousEndomorphismMatrixTrace
import QuaternionicSymmetry.ExteriorMatrixTraceBridge

/-! All-degree actual scalar-line curvature traces in universal exterior
coordinates, with the normalized wedge convention. -/
namespace QuaternionicSymmetry.QuaternionicScalarLineTracePowerForm
open QuaternionicScalarLineNormedCurvature
  QuaternionicScalarLineExteriorCurvature QuaternionicNormedLineBasis
  QuaternionicCurvatureExteriorCoordinates QuaternionicUniversalEvenTrace
  QuaternionicExteriorEvenTrace ExteriorMatrixWedgeBridge
  ExteriorMatrixTraceBridge ContinuousEndomorphismMatrix
  ContinuousEndomorphismMatrixTrace ContinuousAlgebraWedgePowers
  LocalChernWeilTracePowers ManifoldQuaternionicAdjointConnection
open scoped Quaternion ContDiff Manifold
noncomputable section
set_option maxHeartbeats 1000000

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
local instance : NormedSpace ℝ ℍ := inferInstance
local instance : NormedRing (ℍ →L[ℝ] ℍ) := inferInstance
local instance : NormedAlgebra ℝ (ℍ →L[ℝ] ℍ) := inferInstance
local instance : NormedRing (Matrix (Fin 4) (Fin 4) ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix (Fin 4) (Fin 4) ℝ) := Matrix.linftyOpNormedAlgebra

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

def scalarLineCurvatureForm (p : M) (y : E) :
    E [⋀^Fin 2]→L[ℝ] (ℍ →L[ℝ] ℍ) :=
  (QuaternionicProjectiveStandardLie.scalarLineLie
    (Q.reduction.Q (achart E p))).compContinuousAlternatingMap
      (LocalConnectionForms.curvatureForm (D.form p) y)

/-- Exact all-degree trace of actual scalar-line curvature against the
universal quaternionic line exterior matrix. -/
theorem scalarLine_tracePower_eq_exterior (p : M) (y : E) (k : ℕ) :
    LocalEndomorphismTrace.traceCLM.compContinuousAlternatingMap
      (power (scalarLineCurvatureForm Q D p y) k) =
    ExteriorContinuousPairing.toContinuous (powerDegree k)
      (wedgeTrace
        (lineMatrix (liftTwo (fun i => axialCurvaturePower Q D p y i)))
        (line_entries_two (fun i => axialCurvaturePower Q D p y i)) k) := by
  let A := lineMatrix (liftTwo (fun i => axialCurvaturePower Q D p y i))
  let hA := line_entries_two (fun i => axialCurvaturePower Q D p y i)
  let F := scalarLineCurvatureForm Q D p y
  let f : (ℍ →L[ℝ] ℍ) →L[ℝ] Matrix (Fin 4) (Fin 4) ℝ := matrixCLM lineBasis
  have hF : f.compContinuousAlternatingMap F = matrixTwoForm A hA := by
    exact QuaternionicScalarLineNormedCurvature.scalarLineCurvature_matrixTwoForm Q D p y
  have hpow : power (matrixTwoForm A hA) k =
      matrixWedgePower (matrixTwoForm A hA) k := by
    induction k with
    | zero => rfl
    | succ k ih =>
        change ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ
          (Matrix (Fin 4) (Fin 4) ℝ)) (matrixTwoForm A hA)
          (power (matrixTwoForm A hA) k) = _
        rw [ih]
        rfl
  apply ContinuousAlternatingMap.ext
  intro w
  change LocalEndomorphismTrace.traceCLM (power F k w) = _
  calc
    LocalEndomorphismTrace.traceCLM (power F k w) =
      traceCLM (f (power F k w)) := trace_factor_apply lineBasis _
    _ = traceCLM ((matrixWedgePower (matrixTwoForm A hA) k) w) := by
      have hm := congrArg (fun beta : E [⋀^Fin (powerDegree k)]→L[ℝ]
          Matrix (Fin 4) (Fin 4) ℝ => beta w)
        (map_power f (matrixCLM_mul lineBasis) F k)
      rw [hF] at hm
      rw [hpow] at hm
      have hh : f (power F k w) =
          (matrixWedgePower (matrixTwoForm A hA) k) w := by
        change f (power F k w) = (matrixWedgePower (matrixTwoForm A hA) k) w at hm
        exact hm
      exact congrArg traceCLM hh
    _ = ExteriorContinuousPairing.toContinuous (powerDegree k)
        (wedgeTrace A hA k) w := by
      exact congrArg (fun beta : E [⋀^Fin (powerDegree k)]→L[ℝ] ℝ => beta w)
        (trace_matrixWedgePower A hA k)

end
end QuaternionicSymmetry.QuaternionicScalarLineTracePowerForm
