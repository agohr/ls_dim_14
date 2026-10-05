import QuaternionicSymmetry.ProjectiveAdjointDescent
import QuaternionicSymmetry.LocalTraceWordGauge

/-! Descent of ordered cyclic traces of any finite list of curvature
coefficients through the projective atlas.  These are scalar functions for
fixed tangent-vector arguments.  Alternating them into normalized differential
forms, proving their closure, and comparing global characteristic classes
remain distinct obligations. -/

namespace QuaternionicSymmetry.ProjectiveTraceWordDescent

open QuaternionicSymmetry.ProjectiveAdjointDescent
  QuaternionicSymmetry.ProjectiveAdjointDescent.GaugeAtlas
  QuaternionicSymmetry.LocalTraceWordGauge
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionExterior
open scoped Topology

noncomputable section

variable {ι E A B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ A := NormedAlgebra.toNormedSpace A

variable (P : GaugeAtlas ι E A) (D : P.Connection)
  (τ : CyclicTrace (A := A) (B := B))

/-- The cyclic trace of any finite curvature word agrees across overlapping
projective charts, including for the empty word. -/
theorem traceWord_transition (i j : ι) (x : E)
    (hi : x ∈ P.U i) (hj : x ∈ P.U j) (vs : List (Fin 2 → E)) :
    τ.T ((vs.map (fun v => curvatureForm (D.Γ j) x v)).prod) =
      τ.T ((vs.map (fun v => curvatureForm (D.Γ i) x v)).prod) := by
  exact trace_curvature_word_transition τ.T τ.cyclic (D.Γ i) (D.Γ j)
    (P.g i j) (P.g j i) x (D.patch i j x hi hj)
    (D.regular i x hi) (P.regular i j x hi hj)
    ((P.regular j i x hj hi).differentiableAt (by norm_num))
    (P.inverse_germ i j x hi hj) (P.inverse i j x hi hj) vs

/-- A chart-independent scalar function obtained from an arbitrary ordered
word in the descended curvature coefficients. -/
def traceWordSection (vs : List (Fin 2 → E)) (x : E) : B :=
  let i := Classical.choose (P.cover.exists_mem x)
  τ.T ((vs.map (fun v => curvatureForm (D.Γ i) x v)).prod)

theorem traceWordSection_eq_local (vs : List (Fin 2 → E)) (x : E)
    (i : ι) (hi : x ∈ P.U i) :
    traceWordSection P D τ vs x =
      τ.T ((vs.map (fun v => curvatureForm (D.Γ i) x v)).prod) := by
  unfold traceWordSection
  exact (traceWord_transition P D τ _ i x
    (Classical.choose_spec (P.cover.exists_mem x)) hi vs).symm

theorem traceWordSection_germ (vs : List (Fin 2 → E)) (x : E)
    (i : ι) (hi : x ∈ P.U i) :
    traceWordSection P D τ vs =ᶠ[𝓝 x]
      fun y => τ.T ((vs.map (fun v => curvatureForm (D.Γ i) y v)).prod) := by
  filter_upwards [((P.U i).isOpen.mem_nhds hi)] with y hy
  exact traceWordSection_eq_local P D τ vs y i hy

/-- The scalar trace word descended from twice differentiable local
connections is differentiable at every point.  This is regularity of a scalar
function, not closure of a higher characteristic form. -/
theorem differentiableAt_traceWordSection (vs : List (Fin 2 → E))
    (hC2 : ∀ i x, x ∈ P.U i → ContDiffAt ℝ 2 (D.Γ i) x) (x : E) :
    DifferentiableAt ℝ (traceWordSection P D τ vs) x := by
  obtain ⟨i, hi⟩ := P.cover.exists_mem x
  have hΓ : DifferentiableAt ℝ (D.Γ i) x :=
    (hC2 i x hi).differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ (D.Γ i)) x :=
    ((hC2 i x hi).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hF : DifferentiableAt ℝ (curvatureForm (D.Γ i)) x :=
    differentiableAt_curvatureForm (D.Γ i) x hΓ hD
  have hprod : DifferentiableAt ℝ
      (fun y => (vs.map (fun v => curvatureForm (D.Γ i) y v)).prod) x := by
    induction vs with
    | nil => simp
    | cons v vs ih =>
        have hv : DifferentiableAt ℝ (fun y => curvatureForm (D.Γ i) y v) x :=
          hF.continuousAlternatingMap_apply_const v
        simpa only [List.map_cons, List.prod_cons] using hv.mul ih
  have hlocal : DifferentiableAt ℝ
      (fun y => τ.T ((vs.map (fun v => curvatureForm (D.Γ i) y v)).prod)) x :=
    τ.T.differentiableAt.comp x hprod
  exact hlocal.congr_of_eventuallyEq (traceWordSection_germ P D τ vs x i hi)

end
end QuaternionicSymmetry.ProjectiveTraceWordDescent
