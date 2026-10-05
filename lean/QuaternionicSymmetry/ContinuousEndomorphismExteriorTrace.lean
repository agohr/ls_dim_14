import QuaternionicSymmetry.ContinuousMatrixExteriorInverse
import QuaternionicSymmetry.ContinuousAlgebraWedgePowers
import QuaternionicSymmetry.ContinuousEndomorphismMatrixTrace

/-! The exterior trace representative of any endomorphism-valued
alternating two-form agrees with its normalized Chern--Weil wedge trace. -/
namespace QuaternionicSymmetry.ContinuousEndomorphismExteriorTrace
open ContinuousEndomorphismMatrix ContinuousEndomorphismMatrixTrace
  ContinuousMatrixExteriorInverse ExteriorMatrixWedgeBridge
  ExteriorMatrixTraceBridge ContinuousAlgebraWedgePowers
  LocalChernWeilTracePowers
open Module
noncomputable section
set_option maxHeartbeats 1000000

variable {E V κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype κ] [DecidableEq κ]
local instance : NormedRing (Matrix κ κ ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix κ κ ℝ) := Matrix.linftyOpNormedAlgebra

def exteriorEndomorphismMatrix (b : Basis κ ℝ V)
    (F : E [⋀^Fin 2]→L[ℝ] (V →L[ℝ] V)) :
    Matrix κ κ (QuaternionicExteriorEvenTrace.EvenAlgebra E) :=
  exteriorMatrix ((matrixCLM b).compContinuousAlternatingMap F)

theorem trace_power_eq_exterior (b : Basis κ ℝ V)
    (F : E [⋀^Fin 2]→L[ℝ] (V →L[ℝ] V)) (k : ℕ) :
    LocalEndomorphismTrace.traceCLM.compContinuousAlternatingMap (power F k) =
      ExteriorContinuousPairing.toContinuous (powerDegree k)
        (wedgeTrace (exteriorEndomorphismMatrix b F)
          (entries_two ((matrixCLM b).compContinuousAlternatingMap F)) k) := by
  let A := exteriorEndomorphismMatrix b F
  let hA := entries_two ((matrixCLM b).compContinuousAlternatingMap F)
  let f := matrixCLM b
  have hF : f.compContinuousAlternatingMap F = matrixTwoForm A hA := by
    exact (matrixTwoForm_exteriorMatrix _).symm
  have hpow : power (matrixTwoForm A hA) k =
      matrixWedgePower (matrixTwoForm A hA) k := by
    induction k with
    | zero => rfl
    | succ k ih =>
        change ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ
          (Matrix κ κ ℝ)) (matrixTwoForm A hA)
          (power (matrixTwoForm A hA) k) = _
        rw [ih]
        rfl
  apply ContinuousAlternatingMap.ext
  intro w
  change LocalEndomorphismTrace.traceCLM (power F k w) = _
  calc
    LocalEndomorphismTrace.traceCLM (power F k w) =
      traceCLM (f (power F k w)) := trace_factor_apply b _
    _ = traceCLM ((matrixWedgePower (matrixTwoForm A hA) k) w) := by
      have hm := congrArg (fun beta : E [⋀^Fin (powerDegree k)]→L[ℝ]
          Matrix κ κ ℝ => beta w) (map_power f (matrixCLM_mul b) F k)
      rw [hF, hpow] at hm
      exact congrArg traceCLM hm
    _ = ExteriorContinuousPairing.toContinuous (powerDegree k)
        (wedgeTrace A hA k) w := by
      exact congrArg (fun beta : E [⋀^Fin (powerDegree k)]→L[ℝ] ℝ => beta w)
        (trace_matrixWedgePower A hA k)

end
end QuaternionicSymmetry.ContinuousEndomorphismExteriorTrace
