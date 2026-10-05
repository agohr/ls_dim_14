import QuaternionicSymmetry.QuaternionicCurvatureMatrixExpansion
import QuaternionicSymmetry.ContinuousAlgebraWedgePowers
import QuaternionicSymmetry.LocalEndomorphismTrace

/-! Removing the zero quaternionic line preserves every positive actual
curvature wedge trace, independently of the matrix bases on the two spaces. -/
namespace QuaternionicSymmetry.QuaternionicUpperBlockTraceForms
open QuaternionicCurvatureMatrixExpansion QuaternionicProjectiveStandardL2
open ContinuousAlgebraWedgePowers LocalEndomorphismTrace
noncomputable section
open scoped Quaternion
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance
local instance : NormedRing (E →L[ℝ] E) := inferInstance
local instance : NormedAlgebra ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedRing (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) := inferInstance
local instance : NormedAlgebra ℝ (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) := inferInstance

def upperCLM : (E →L[ℝ] E) →L[ℝ]
    (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) :=
  upperEmbedding.toContinuousLinearMap

theorem upperCLM_mul (A B : E →L[ℝ] E) : upperCLM (A * B) = upperCLM A * upperCLM B := by
  apply ContinuousLinearMap.ext
  intro z
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
  rfl

theorem upperCLM_trace (A : E →L[ℝ] E) : traceCLM (upperCLM A) = traceCLM A := by
  let c := WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ
  have hb : c.toLinearEquiv.conj (upperCLM A).toLinearMap =
      LinearMap.prodMap A.toLinearMap (0 : ℍ →ₗ[ℝ] ℍ) := by
    apply LinearMap.ext
    intro z
    rfl
  have ht := LinearMap.trace_conj' (upperCLM A).toLinearMap c.toLinearEquiv
  rw [hb, LinearMap.trace_prodMap', map_zero, add_zero] at ht
  exact ht.symm

theorem trace_power_upper (α : V [⋀^Fin 2]→L[ℝ] (E →L[ℝ] E))
    (k : ℕ) (v : Fin (LocalChernWeilTracePowers.powerDegree k) → V) :
    traceCLM (power (upperCLM.compContinuousAlternatingMap α) k v) =
      traceCLM (power α k v) := by
  have h := congrArg (fun β => β v) (map_power upperCLM upperCLM_mul α k)
  change upperCLM (power α k v) = _ at h
  exact (congrArg traceCLM h).symm.trans (upperCLM_trace _)

end
end QuaternionicSymmetry.QuaternionicUpperBlockTraceForms
