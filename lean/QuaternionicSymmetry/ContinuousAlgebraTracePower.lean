import QuaternionicSymmetry.ContinuousAlgebraWedgePower
import QuaternionicSymmetry.ExteriorMatrixTraceBridge

/-! Trace of an ordered algebra-valued wedge power after a multiplicative
matrix coordinate map. -/
namespace QuaternionicSymmetry.ContinuousAlgebraTracePower
open ContinuousAlgebraWedgePower ExteriorMatrixWedgeBridge
  ExteriorMatrixTraceBridge LocalChernWeilTracePowers
  QuaternionicExteriorEvenTrace EvenForms ExteriorContinuousPairing
noncomputable section

variable {E R κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedRing R] [NormedAlgebra ℝ R]
  [Fintype κ] [DecidableEq κ]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R
local instance : NormedRing (Matrix κ κ ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix κ κ ℝ) := Matrix.linftyOpNormedAlgebra

theorem trace_orderedPower (f : R →L[ℝ] Matrix κ κ ℝ)
    (hmul : ∀ a b : R, f (a * b) = f a * f b)
    (τ : R →L[ℝ] ℝ)
    (htrace : ∀ a : R, τ a = traceCLM (f a))
    (F : E [⋀^Fin 2]→L[ℝ] R)
    (A : Matrix κ κ (EvenAlgebra E))
    (hA : ∀ i j, ((A i j : EvenAlgebra E) :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈
        ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E))
    (hF : f.compContinuousAlternatingMap F = matrixTwoForm A hA)
    (k : ℕ) :
    τ.compContinuousAlternatingMap (orderedPower F k) =
      toContinuous (powerDegree k) (wedgeTrace A hA k) := by
  apply ContinuousAlternatingMap.ext
  intro w
  change τ (orderedPower F k w) = _
  calc
    τ (orderedPower F k w) =
      traceCLM (f (orderedPower F k w)) := htrace _
    _ = traceCLM ((matrixWedgePower (matrixTwoForm A hA) k) w) := by
      have h := congrArg (fun α : E [⋀^Fin (powerDegree k)]→L[ℝ]
          Matrix κ κ ℝ => α w)
        (map_orderedPower f hmul F (matrixTwoForm A hA) hF k)
      exact congrArg traceCLM h
    _ = toContinuous (powerDegree k) (wedgeTrace A hA k) w := by
      exact congrArg (fun α : E [⋀^Fin (powerDegree k)]→L[ℝ] ℝ => α w)
        (trace_matrixWedgePower A hA k)

end
end QuaternionicSymmetry.ContinuousAlgebraTracePower
