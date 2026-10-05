import QuaternionicSymmetry.QuaternionicAdjointExteriorCurvature
import QuaternionicSymmetry.LocalChernWeilMatrixTraceBridge
import QuaternionicSymmetry.ContinuousEndomorphismMatrixTrace

/-! All positive Chern--Weil trace powers of the actual induced rank-three
connection are the canonical pairings of the universal exterior adjoint
matrix powers. -/
namespace QuaternionicSymmetry.QuaternionicAdjointTracePowerForm
open QuaternionicAdjointExteriorCurvature QuaternionicCurvatureExteriorCoordinates
  QuaternionicUniversalEvenTrace QuaternionicExteriorEvenTrace
  ExteriorMatrixWedgeBridge ExteriorMatrixTraceBridge
  ContinuousEndomorphismMatrix ContinuousEndomorphismMatrixTrace
  LocalChernWeilTracePowers LocalChernWeilMatrixMap
  LocalChernWeilMatrixTraceBridge ManifoldQuaternionicAdjointConnection
open scoped ContDiff Manifold
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

local instance : NormedRing (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.linftyOpNormedAlgebra

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem induced_tracePowerForm_eq_exterior (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (k : ℕ) :
    tracePowerForm LocalEndomorphismTrace.traceCLM (inducedForm Q D p) k y =
      ExteriorContinuousPairing.toContinuous (powerDegree k)
        (wedgeTrace
          (adjointMatrix (liftTwo (fun i => axialCurvaturePower Q D p y i)))
          (QuaternionicAdjointExteriorCurvature.adjoint_entries_two
            (fun i => axialCurvaturePower Q D p y i)) k) := by
  let omegaForms : Fin 3 → ExteriorContinuousPairing.Power E 2 :=
    fun i => axialCurvaturePower Q D p y i
  let A := adjointMatrix (liftTwo omegaForms)
  let hA := QuaternionicAdjointExteriorCurvature.adjoint_entries_two omegaForms
  let f := matrixCLM (Pi.basisFun ℝ (Fin 3))
  let γ := matrixTwoForm A hA
  have hγ : f.compContinuousAlternatingMap
      (LocalConnectionForms.curvatureForm (inducedForm Q D p) y) = γ := by
    exact inducedCurvature_matrixTwoForm Q D p y hy
  apply ContinuousAlternatingMap.ext
  intro w
  change LocalEndomorphismTrace.traceCLM
    (curvaturePowerForm (inducedForm Q D p) k y w) = _
  calc
    LocalEndomorphismTrace.traceCLM
        (curvaturePowerForm (inducedForm Q D p) k y w) =
      traceCLM (f (curvaturePowerForm (inducedForm Q D p) k y w)) :=
        trace_factor_apply (Pi.basisFun ℝ (Fin 3)) _
    _ = traceCLM ((mappedPower f (inducedForm Q D p) y k) w) := by
      have h := congrArg (fun α : E [⋀^Fin (powerDegree k)]→L[ℝ]
          Matrix (Fin 3) (Fin 3) ℝ => α w)
        (map_curvaturePowerForm f (matrixCLM_mul _) (inducedForm Q D p) y k)
      exact congrArg traceCLM h
    _ = traceCLM ((matrixWedgePower γ k) w) := by
      rw [mappedPower_eq f (inducedForm Q D p) y γ hγ k]
    _ = ExteriorContinuousPairing.toContinuous (powerDegree k)
        (wedgeTrace A hA k) w := by
      exact congrArg (fun α : E [⋀^Fin (powerDegree k)]→L[ℝ] ℝ => α w)
        (trace_matrixWedgePower A hA k)

end
end QuaternionicSymmetry.QuaternionicAdjointTracePowerForm
