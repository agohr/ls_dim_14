import QuaternionicSymmetry.ProjectiveAdjointDescent
import QuaternionicSymmetry.LocalChernWeilQuadraticTransgression
import QuaternionicSymmetry.LocalChernWeilQuadraticVariation
import QuaternionicSymmetry.LocalChernWeilQuadraticTransgressionFTC
import QuaternionicSymmetry.LocalChernWeilQuadraticTransgressionExact
import QuaternionicSymmetry.CyclicTraceConjugation

/-! The quadratic transgression integrand `T(θ ∧ F)` descends through an
indexed projective atlas.  Here `θ` is an adjoint-valued variation of a
connection, so this three-form has a homogeneous gauge law.  No global PQK
atlas, de Rham class, or integration theorem is supplied by the declaration. -/

namespace QuaternionicSymmetry.ProjectiveQuadraticTransgression

open QuaternionicSymmetry.ProjectiveAdjointDescent
  QuaternionicSymmetry.ProjectiveAdjointDescent.GaugeAtlas
  QuaternionicSymmetry.LocalChernWeilQuadraticTransgression
  QuaternionicSymmetry.LocalChernWeilQuadraticVariation
  QuaternionicSymmetry.LocalChernWeilQuadraticTransgressionFTC
  QuaternionicSymmetry.LocalChernWeilQuadraticTransgressionExact
  QuaternionicSymmetry.LocalChernWeilQuadratic
  QuaternionicSymmetry.CyclicTraceConjugation
  QuaternionicSymmetry.LocalConnectionGauge
  QuaternionicSymmetry.LocalConnectionForms
open scoped Topology

noncomputable section

variable {ι E A B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ A := NormedAlgebra.toNormedSpace A

variable (P : GaugeAtlas ι E A) (D : P.Connection)
  (Θ : P.AdjointOneForm) (τ : CyclicTrace (A := A) (B := B))

/-- The variation-curvature three-form is independent of the projective
gauge chart.  The proof uses actual local transition laws for both forms. -/
theorem traceConnectionCurvature_transition (i j : ι) (x : E)
    (hi : x ∈ P.U i) (hj : x ∈ P.U j) :
    traceConnectionCurvature τ.T (D.Γ i) (Θ.θ i) x =
      traceConnectionCurvature τ.T (D.Γ j) (Θ.θ j) x := by
  have hθ (v : E) : Θ.θ j x v =
      P.g j i x * (Θ.θ i x v * P.g i j x) := by
    have hp := (Θ.patch i j x hi hj).eq_of_nhds
    have hv := congrArg (fun f : E →L[ℝ] A => f v) hp
    simpa only [adjointForm_apply] using hv
  have hF (v w : E) :
      LocalConnection.curvature (D.Γ j) x v w =
        P.g j i x *
          (LocalConnection.curvature (D.Γ i) x v w * P.g i j x) := by
    simpa only [curvatureForm_apply, mul_assoc] using
      P.curvature_transition D i j x hi hj ![v, w]
  have hpair (a b : A) :
      τ.T ((P.g j i x * (a * P.g i j x)) *
        (P.g j i x * (b * P.g i j x))) = τ.T (a * b) := by
    have h := cyclic_trace_conjugated_list_prod τ.T τ.cyclic
      (P.g i j x) (P.g j i x)
      (P.inverse i j x hi hj) (P.inverse j i x hj hi) [a, b]
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_assoc] using h
  ext v
  have hv : v = ![v 0, v 1, v 2] := by
    ext k
    fin_cases k <;> rfl
  rw [hv]
  simp only [traceConnectionCurvature_apply]
  rw [hθ (v 0), hθ (v 1), hθ (v 2),
    hF (v 1) (v 2), hF (v 0) (v 2), hF (v 0) (v 1)]
  simp only [map_sub, map_add]
  rw [hpair (Θ.θ i x (v 0)) (LocalConnection.curvature (D.Γ i) x (v 1) (v 2)),
    hpair (Θ.θ i x (v 1)) (LocalConnection.curvature (D.Γ i) x (v 0) (v 2)),
    hpair (Θ.θ i x (v 2)) (LocalConnection.curvature (D.Γ i) x (v 0) (v 1))]

/-- The descended, chart-independent quadratic transgression integrand. -/
def transgressionSection (x : E) : E [⋀^Fin 3]→L[ℝ] B :=
  let i := Classical.choose (P.cover.exists_mem x)
  traceConnectionCurvature τ.T (D.Γ i) (Θ.θ i) x

theorem transgressionSection_eq_local (x : E) (i : ι) (hi : x ∈ P.U i) :
    transgressionSection P D Θ τ x =
      traceConnectionCurvature τ.T (D.Γ i) (Θ.θ i) x := by
  unfold transgressionSection
  exact traceConnectionCurvature_transition P D Θ τ _ i x
    (Classical.choose_spec (P.cover.exists_mem x)) hi

theorem transgressionSection_germ (x : E) (i : ι) (hi : x ∈ P.U i) :
    transgressionSection P D Θ τ =ᶠ[𝓝 x]
      traceConnectionCurvature τ.T (D.Γ i) (Θ.θ i) := by
  filter_upwards [((P.U i).isOpen.mem_nhds hi)] with y hy
  exact transgressionSection_eq_local P D Θ τ y i hy

/-- The gauge-independent transgression integrand along the entire affine
connection path. -/
def pathTransgressionSection (t : ℝ) : E → E [⋀^Fin 3]→L[ℝ] B :=
  transgressionSection P (P.pathConnection D Θ t) Θ τ

theorem pathTransgressionSection_eq_local (t : ℝ) (x : E)
    (i : ι) (hi : x ∈ P.U i) :
    pathTransgressionSection P D Θ τ t x =
      traceConnectionCurvature τ.T (D.Γ i + t • Θ.θ i) (Θ.θ i) x :=
  transgressionSection_eq_local P (P.pathConnection D Θ t) Θ τ x i hi

/-- The curvature-square section of the projective connection path has its
actual pointwise derivative, computed in any chart.  No class is invoked. -/
theorem traceSquareSection_path_hasDerivAt (x : E) (i : ι)
    (hi : x ∈ P.U i) (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
        traceSquareSection P (P.pathConnection D Θ s) τ x)
      (wedge22 (traceProduct τ.T)
          (covariantDerivativeForm (D.Γ i + t • Θ.θ i) (Θ.θ i) x)
          (curvatureForm (D.Γ i + t • Θ.θ i) x) +
        wedge22 (traceProduct τ.T)
          (curvatureForm (D.Γ i + t • Θ.θ i) x)
          (covariantDerivativeForm (D.Γ i + t • Θ.θ i) (Θ.θ i) x)) t := by
  have hfun : (fun s : ℝ =>
      traceSquareSection P (P.pathConnection D Θ s) τ x) =
      (fun s : ℝ => traceSquareForm τ.T (D.Γ i + s • Θ.θ i) x) := by
    funext s
    exact traceSquareSection_eq_local P (P.pathConnection D Θ s) τ x i hi
  rw [hfun]
  exact traceSquareForm_path_hasDerivAt τ.T (D.Γ i) (Θ.θ i) x
    (D.regular i x hi) (Θ.regular i x hi) t

/-- The derivative of the descended quadratic form along the projective
connection path is the exterior derivative of the descended transgression
three-form.  This is an identity of local differential forms on the covered
normed space, not a comparison of de Rham classes on a PQK manifold. -/
theorem traceSquareSection_path_hasDerivAt_extDeriv
    (hD2 : ∀ i x, x ∈ P.U i → ContDiffAt ℝ 2 (D.Γ i) x)
    (hΘ2 : ∀ i x, x ∈ P.U i → ContDiffAt ℝ 2 (Θ.θ i) x)
    (x : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
        traceSquareSection P (P.pathConnection D Θ s) τ x)
      ((2 : ℝ) • extDeriv (pathTransgressionSection P D Θ τ t) x) t := by
  obtain ⟨i, hi⟩ := P.cover.exists_mem x
  have hΓpath : ContDiffAt ℝ 2 (D.Γ i + t • Θ.θ i) x :=
    (hD2 i x hi).add ((hΘ2 i x hi).const_smul t)
  have hgerm : pathTransgressionSection P D Θ τ t =ᶠ[𝓝 x]
      traceConnectionCurvature τ.T (D.Γ i + t • Θ.θ i) (Θ.θ i) := by
    simpa only [pathTransgressionSection] using
      transgressionSection_germ P (P.pathConnection D Θ t) Θ τ x i hi
  have hvariation :
      wedge22 (traceProduct τ.T)
          (covariantDerivativeForm (D.Γ i + t • Θ.θ i) (Θ.θ i) x)
          (curvatureForm (D.Γ i + t • Θ.θ i) x) +
        wedge22 (traceProduct τ.T)
          (curvatureForm (D.Γ i + t • Θ.θ i) x)
          (covariantDerivativeForm (D.Γ i + t • Θ.θ i) (Θ.θ i) x) =
        (2 : ℝ) • extDeriv (pathTransgressionSection P D Θ τ t) x := by
    rw [hgerm.extDeriv_eq]
    rw [extDeriv_traceConnectionCurvature τ.T τ.cyclic
      (D.Γ i + t • Θ.θ i) (Θ.θ i) x hΓpath (Θ.regular i x hi)]
    rw [wedge22_cyclic (traceProduct τ.T) (fun a b => τ.cyclic a b)
      (curvatureForm (D.Γ i + t • Θ.θ i) x)
      (covariantDerivativeForm (D.Γ i + t • Θ.θ i) (Θ.θ i) x)]
    module
  rw [← hvariation]
  exact traceSquareSection_path_hasDerivAt P D Θ τ x i hi t

/-- The endpoint difference of the descended quadratic form is an integral
of exterior derivatives of descended three-forms.  Passing `extDeriv` through
this time integral and then to a cohomology class is still a separate step. -/
theorem traceSquareSection_sub_eq_integral_extDeriv [CompleteSpace B]
    (hD2 : ∀ i x, x ∈ P.U i → ContDiffAt ℝ 2 (D.Γ i) x)
    (hΘ2 : ∀ i x, x ∈ P.U i → ContDiffAt ℝ 2 (Θ.θ i) x)
    (x : E) :
    traceSquareSection P (P.pathConnection D Θ 1) τ x -
      traceSquareSection P D τ x =
        ∫ t in (0 : ℝ)..1,
          (2 : ℝ) • extDeriv (pathTransgressionSection P D Θ τ t) x := by
  obtain ⟨i, hi⟩ := P.cover.exists_mem x
  have hpath1 :
      traceSquareSection P (P.pathConnection D Θ 1) τ x =
        traceSquareForm τ.T (D.Γ i + Θ.θ i) x := by
    have h := traceSquareSection_eq_local P (P.pathConnection D Θ 1) τ x i hi
    change _ = traceSquareForm τ.T (D.Γ i + (1 : ℝ) • Θ.θ i) x at h
    simpa only [one_smul] using h
  have hbase : traceSquareSection P D τ x =
      traceSquareForm τ.T (D.Γ i) x :=
    traceSquareSection_eq_local P D τ x i hi
  rw [hpath1, hbase]
  rw [traceSquareForm_sub_eq_integral_extDeriv τ.T τ.cyclic
    (D.Γ i) (Θ.θ i) x (hD2 i x hi) (hΘ2 i x hi)]
  congr 1
  funext t
  have hgerm : pathTransgressionSection P D Θ τ t =ᶠ[𝓝 x]
      traceConnectionCurvature τ.T (D.Γ i + t • Θ.θ i) (Θ.θ i) := by
    simpa only [pathTransgressionSection] using
      transgressionSection_germ P (P.pathConnection D Θ t) Θ τ x i hi
  rw [hgerm.extDeriv_eq]

/-- The integrated three-form is globally defined on the supplied projective
atlas because every path integrand descends. -/
def integratedTransgressionSection [CompleteSpace B] (x : E) :
    E [⋀^Fin 3]→L[ℝ] B :=
  ∫ t in (0 : ℝ)..1,
    (2 : ℝ) • pathTransgressionSection P D Θ τ t x

theorem integratedTransgressionSection_germ [CompleteSpace B]
    (x : E) (i : ι) (hi : x ∈ P.U i) :
    integratedTransgressionSection P D Θ τ =ᶠ[𝓝 x]
      (fun y => ∫ t in (0 : ℝ)..1,
        (2 : ℝ) • traceConnectionCurvature τ.T
          (D.Γ i + t • Θ.θ i) (Θ.θ i) y) := by
  filter_upwards [((P.U i).isOpen.mem_nhds hi)] with y hy
  unfold integratedTransgressionSection
  apply intervalIntegral.integral_congr
  intro t _
  change (2 : ℝ) • pathTransgressionSection P D Θ τ t y =
    (2 : ℝ) • traceConnectionCurvature τ.T
      (D.Γ i + t • Θ.θ i) (Θ.θ i) y
  rw [pathTransgressionSection_eq_local P D Θ τ t y i hy]

/-- On the supplied projective atlas, the two descended quadratic trace
forms differ by the exterior derivative of one descended three-form. -/
theorem traceSquareSection_sub_eq_extDeriv [CompleteSpace B]
    (hD2 : ∀ i x, x ∈ P.U i → ContDiffAt ℝ 2 (D.Γ i) x)
    (hΘ2 : ∀ i x, x ∈ P.U i → ContDiffAt ℝ 2 (Θ.θ i) x)
    (x : E) :
    traceSquareSection P (P.pathConnection D Θ 1) τ x -
      traceSquareSection P D τ x =
        extDeriv (integratedTransgressionSection P D Θ τ) x := by
  obtain ⟨i, hi⟩ := P.cover.exists_mem x
  have hpath1 :
      traceSquareSection P (P.pathConnection D Θ 1) τ x =
        traceSquareForm τ.T (D.Γ i + Θ.θ i) x := by
    have h := traceSquareSection_eq_local P (P.pathConnection D Θ 1) τ x i hi
    change _ = traceSquareForm τ.T (D.Γ i + (1 : ℝ) • Θ.θ i) x at h
    simpa only [one_smul] using h
  have hbase : traceSquareSection P D τ x =
      traceSquareForm τ.T (D.Γ i) x :=
    traceSquareSection_eq_local P D τ x i hi
  rw [hpath1, hbase,
    (integratedTransgressionSection_germ P D Θ τ x i hi).extDeriv_eq]
  exact traceSquareForm_sub_eq_extDeriv_integral τ.T τ.cyclic
    (D.Γ i) (Θ.θ i) x (hD2 i x hi) (hΘ2 i x hi)

end
end QuaternionicSymmetry.ProjectiveQuadraticTransgression
