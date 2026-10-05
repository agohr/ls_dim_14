import QuaternionicSymmetry.QuaternionicComplexMatrixAlgebra
import QuaternionicSymmetry.ContinuousAlgebraWedgePowers

/-! Actual continuous quaternion-linear endomorphism two-forms have fixed
complex matrix coordinates in every wedge degree, with exact real/complex
trace factor two. -/
namespace QuaternionicSymmetry.QuaternionicMatrixTwoFormTrace
open QuaternionicComplexMatrixAlgebra ContinuousAlgebraWedgePowers
open LocalChernWeilTracePowers LocalEndomorphismTrace
noncomputable section
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable (S : QuaternionicStructure V)
local instance : NormedSpace ℝ V := inferInstance
local instance : NormedRing (V →L[ℝ] V) := inferInstance
local instance : NormedAlgebra ℝ (V →L[ℝ] V) := inferInstance
local instance : NormedRing (complexLinearAlgebra S) := inferInstance
local instance : NormedAlgebra ℝ (complexLinearAlgebra S) := inferInstance
local instance : NormedRing (Matrix
    (Fin S.quaternionicDimension ⊕ Fin S.quaternionicDimension)
    (Fin S.quaternionicDimension ⊕ Fin S.quaternionicDimension) ℂ) :=
  Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix
    (Fin S.quaternionicDimension ⊕ Fin S.quaternionicDimension)
    (Fin S.quaternionicDimension ⊕ Fin S.quaternionicDimension) ℂ) :=
  Matrix.linftyOpNormedAlgebra
variable (α : E [⋀^Fin 2]→L[ℝ] (V →L[ℝ] V))
  (hα : ∀ (v : Fin 2 → E) (w : V), α v (S.I w) = S.I (α v w))

def restricted : E [⋀^Fin 2]→L[ℝ] complexLinearAlgebra S :=
  α.codRestrict (complexLinearAlgebra S).toSubmodule
    (fun v => (mem_complexLinearAlgebra S (α v)).mpr (hα v))

def matrixForm : E [⋀^Fin 2]→L[ℝ]
    Matrix (Fin S.quaternionicDimension ⊕ Fin S.quaternionicDimension)
      (Fin S.quaternionicDimension ⊕ Fin S.quaternionicDimension) ℂ :=
  (matrixCLM S).compContinuousAlternatingMap (restricted S α hα)

theorem trace_power (k : ℕ) (v : Fin (powerDegree k) → E) :
    traceCLM (power α k v) = 2 * (power (matrixForm S α hα) k v).trace.re := by
  let incl := (complexLinearAlgebra S).toSubmodule.subtypeL
  have hincl : incl.compContinuousAlternatingMap (restricted S α hα) = α := rfl
  have hi := map_power incl (fun _ _ => rfl) (restricted S α hα) k
  rw [hincl] at hi
  have hv := congrArg (fun β : E [⋀^Fin (powerDegree k)]→L[ℝ] (V →L[ℝ] V) => β v) hi
  have hm := map_power (matrixCLM S) (matrixCLM_mul S) (restricted S α hα) k
  have hmv := congrArg (fun β => β v) hm
  calc
    traceCLM (power α k v) = traceCLM (power (restricted S α hα) k v).val :=
      congrArg traceCLM hv.symm
    _ = 2 * (matrixCLM S (power (restricted S α hα) k v)).trace.re := matrixCLM_trace S _
    _ = 2 * (power (matrixForm S α hα) k v).trace.re :=
      congrArg (fun B => 2 * B.trace.re) hmv

end
end QuaternionicSymmetry.QuaternionicMatrixTwoFormTrace
