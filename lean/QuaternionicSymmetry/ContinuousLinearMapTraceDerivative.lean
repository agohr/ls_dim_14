import QuaternionicSymmetry.ManifoldQuaternionicMetric
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Trace

/-! A continuous real trace on finite-dimensional Euclidean endomorphisms,
and its derivative through a differentiable operator-valued field. -/
namespace QuaternionicSymmetry.ContinuousLinearMapTraceDerivative
open scoped Topology
noncomputable section
variable {V X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
local instance : NormedSpace ℝ V := inferInstance

private def realInnerCLM : V →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ (innerₗ V) 1 (fun x y => by
    simpa only [one_mul, innerₗ_apply_apply] using norm_inner_le_norm x y)

def realTraceCLM : (V →L[ℝ] V) →L[ℝ] ℝ :=
  ∑ i : Fin (Module.finrank ℝ V),
    (realInnerCLM (V := V) (stdOrthonormalBasis ℝ V i)).comp
      (ContinuousLinearMap.apply ℝ V (stdOrthonormalBasis ℝ V i))

theorem realTraceCLM_apply (A : V →L[ℝ] V) :
    realTraceCLM A = LinearMap.trace ℝ V A.toLinearMap := by
  rw [realTraceCLM, ContinuousLinearMap.sum_apply,
    LinearMap.trace_eq_sum_inner A.toLinearMap (stdOrthonormalBasis ℝ V)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    realInnerCLM, LinearMap.mkContinuous₂_apply, innerₗ_apply_apply]
  rfl

theorem fderiv_realTraceCLM (F : X → V →L[ℝ] V) (x : X)
    (hF : DifferentiableAt ℝ F x) :
    fderiv ℝ (fun y => realTraceCLM (F y)) x =
      realTraceCLM.comp (fderiv ℝ F x) := by
  have ht : HasFDerivAt (realTraceCLM (V := V))
      (realTraceCLM (V := V)) (F x) :=
    (realTraceCLM (V := V)).hasFDerivAt
  simpa only [Function.comp_def] using (ht.comp x hF.hasFDerivAt).fderiv

end
end QuaternionicSymmetry.ContinuousLinearMapTraceDerivative
