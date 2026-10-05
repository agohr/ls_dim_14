import QuaternionicSymmetry.ProjectiveTraceWordDescent
import QuaternionicSymmetry.LocalChernWeilHigherVariation

/-!
# Derivatives of descended curvature trace words

The trace of an arbitrary finite ordered curvature word already descends
through a supplied projective gauge atlas.  Its actual Frechet derivative is
computed in any chart by the corresponding covariant slot variation.  This
is a scalar derivative identity, not yet a higher Chern--Weil closure or
characteristic-class statement.
-/

namespace QuaternionicSymmetry.ProjectiveHigherTraceVariation

open QuaternionicSymmetry.ProjectiveAdjointDescent
  QuaternionicSymmetry.ProjectiveAdjointDescent.GaugeAtlas
  QuaternionicSymmetry.ProjectiveTraceWordDescent
  QuaternionicSymmetry.LocalChernWeilHigherVariation
open scoped Topology

noncomputable section

variable {ι E A B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ A := NormedAlgebra.toNormedSpace A

/-- Local formula for the derivative of the chart-independent scalar trace
of any finite curvature word.  Only the chosen chart's connection needs
second-order regularity at the point. -/
theorem fderiv_traceWordSection
    (P : GaugeAtlas ι E A) (D : P.Connection)
    (τ : CyclicTrace (A := A) (B := B))
    (vs : List (Fin 2 → E)) (x u : E) (i : ι) (hi : x ∈ P.U i)
    (hΓ : ContDiffAt ℝ 2 (D.Γ i) x) :
    fderiv ℝ (traceWordSection P D τ vs) x u =
      τ.T (curvatureWordVariation (D.Γ i) vs x u) := by
  have hlocal : (fun y => τ.T
      ((vs.map (fun v => LocalConnectionForms.curvatureForm (D.Γ i) y v)).prod)) =
      (fun y => τ.T (curvatureWordProduct (D.Γ i) vs y)) := by
    funext y
    rw [curvatureWordProduct_eq_formWord]
  rw [(traceWordSection_germ P D τ vs x i hi).fderiv_eq (𝕜 := ℝ), hlocal]
  exact fderiv_trace_curvatureWordProduct τ.T τ.cyclic (D.Γ i) vs x u hΓ

end
end QuaternionicSymmetry.ProjectiveHigherTraceVariation
