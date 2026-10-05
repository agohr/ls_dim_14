import QuaternionicSymmetry.ProjectiveHigherTraceForms
import QuaternionicSymmetry.LocalContinuousWedgeGauge
import QuaternionicSymmetry.LocalChernWeilLinear

/-!
# Linear trace transgression on a supplied projective gauge atlas

The degree-one curvature trace is the base case of the higher trace-power
sections. Its connection-difference primitive is a chart-independent one-form
on the same supplied normed-space atlas and requires no time integration.
-/

namespace QuaternionicSymmetry.ProjectiveAdjointDescent.GaugeAtlas

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionGauge
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalChernWeilLinear
  QuaternionicSymmetry.LocalContinuousWedgeGauge

open scoped Topology

noncomputable section

variable {ι E A B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance linearTraceTransgressionNormedSpace : NormedSpace ℝ A :=
  NormedAlgebra.toNormedSpace A

variable (P : GaugeAtlas ι E A) (Θ : P.AdjointOneForm)
  (τ : CyclicTrace (A := A) (B := B))

/-- The degree-one trace primitive `Tθ` agrees across projective overlaps. -/
theorem traceLinearPrimitive_transition (i j : ι) (x : E)
    (hi : x ∈ P.U i) (hj : x ∈ P.U j) :
    τ.T.compContinuousAlternatingMap (connectionForm (Θ.θ i) x) =
      τ.T.compContinuousAlternatingMap (connectionForm (Θ.θ j) x) := by
  have hθ : connectionForm (Θ.θ j) x =
      conjugateForm (P.g i j x) (P.g j i x)
        (connectionForm (Θ.θ i) x) := by
    ext v
    have hp := (Θ.patch i j x hi hj).eq_of_nhds
    have hv := congrArg (fun f : E →L[ℝ] A => f (v 0)) hp
    simpa only [connectionForm, oneFormMap_apply, adjointForm_apply,
      conjugateForm_apply] using hv
  rw [hθ]
  exact (cyclic_conjugateForm τ.T τ.cyclic (P.g i j x) (P.g j i x)
    (P.inverse i j x hi hj) (connectionForm (Θ.θ i) x)).symm

/-- The descended one-form `Tθ`, which is the linear Chern--Weil primitive. -/
def traceLinearPrimitiveSection (x : E) : E [⋀^Fin 1]→L[ℝ] B :=
  let i := Classical.choose (P.cover.exists_mem x)
  τ.T.compContinuousAlternatingMap (connectionForm (Θ.θ i) x)

theorem traceLinearPrimitiveSection_eq_local (x : E) (i : ι)
    (hi : x ∈ P.U i) :
    traceLinearPrimitiveSection P Θ τ x =
      τ.T.compContinuousAlternatingMap (connectionForm (Θ.θ i) x) := by
  unfold traceLinearPrimitiveSection
  exact traceLinearPrimitive_transition P Θ τ _ i x
    (Classical.choose_spec (P.cover.exists_mem x)) hi

theorem traceLinearPrimitiveSection_germ (x : E) (i : ι)
    (hi : x ∈ P.U i) :
    traceLinearPrimitiveSection P Θ τ =ᶠ[𝓝 x]
      (fun y => τ.T.compContinuousAlternatingMap (connectionForm (Θ.θ i) y)) := by
  filter_upwards [((P.U i).isOpen.mem_nhds hi)] with y hy
  exact traceLinearPrimitiveSection_eq_local P Θ τ y i hy

/-- Exact affine-path endpoint for the first curvature trace power on the
supplied projective atlas. Only differentiability of the local connections
and adjoint path direction is required. -/
theorem tracePowerSection_sub_eq_extDeriv_linear (D : P.Connection) (x : E) :
    tracePowerSection P (P.pathConnection D Θ 1) τ 0 x -
      tracePowerSection P D τ 0 x =
        extDeriv (traceLinearPrimitiveSection P Θ τ) x := by
  obtain ⟨i, hi⟩ := P.cover.exists_mem x
  rw [tracePowerSection_eq_local P (P.pathConnection D Θ 1) τ 0 x i hi,
    tracePowerSection_eq_local P D τ 0 x i hi,
    (traceLinearPrimitiveSection_germ P Θ τ x i hi).extDeriv_eq]
  change characteristicForm τ.T (D.Γ i + (1 : ℝ) • Θ.θ i) x -
      characteristicForm τ.T (D.Γ i) x = _
  have h := transgression τ.T τ.cyclic (D.Γ i)
    (D.Γ i + Θ.θ i) x (D.regular i x hi)
    ((D.regular i x hi).add (Θ.regular i x hi))
  simpa only [one_smul, add_sub_cancel_left, DifferentialFormCoefficient.mapForm]
    using h

end
end QuaternionicSymmetry.ProjectiveAdjointDescent.GaugeAtlas
