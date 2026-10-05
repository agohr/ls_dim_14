import QuaternionicSymmetry.ProjectiveHigherTraceForms
import QuaternionicSymmetry.LocalTracePowerPrimitiveGauge
import QuaternionicSymmetry.LocalChernWeilStandardExact
import QuaternionicSymmetry.ProjectiveQuadraticTransgression

/-!
# Higher trace-power transgression on a supplied projective gauge atlas

The normalized local form `T(θ ∧ F^(k+1))` obeys the actual overlap law when
`θ` is an adjoint-valued variation. Its integral along the affine connection
path therefore defines a chart-independent differential form. The endpoint
identity is an equality of actual forms on the covered normed vector space;
no PQK-derived atlas or cohomology class is constructed here.
-/

namespace QuaternionicSymmetry.ProjectiveAdjointDescent.GaugeAtlas

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalChernWeilPowerTransgressionForm
  QuaternionicSymmetry.LocalChernWeilOrderedTransgression
  QuaternionicSymmetry.LocalChernWeilStandardExact
open scoped Topology

noncomputable section

variable {ι E A B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance higherTraceTransgressionNormedSpace : NormedSpace ℝ A :=
  NormedAlgebra.toNormedSpace A

variable (P : GaugeAtlas ι E A) (D : P.Connection)
  (Θ : P.AdjointOneForm) (τ : CyclicTrace (A := A) (B := B))

/-- The normalized `T(θ ∧ F^(k+1))` form agrees on overlaps. -/
theorem tracePowerPrimitive_transition (k : ℕ) (i j : ι) (x : E)
    (hi : x ∈ P.U i) (hj : x ∈ P.U j) :
    traceConnectionCurvaturePower τ.T (D.Γ i) (Θ.θ i) k x =
      traceConnectionCurvaturePower τ.T (D.Γ j) (Θ.θ j) k x := by
  exact (QuaternionicSymmetry.LocalTracePowerPrimitiveGauge.traceConnectionCurvaturePower_transition
      τ.T τ.cyclic
      (D.Γ i) (D.Γ j) (Θ.θ i) (Θ.θ j)
      (P.g i j) (P.g j i) x
      (D.patch i j x hi hj) (Θ.patch i j x hi hj)
      (D.regular i x hi) (P.regular i j x hi hj)
      ((P.regular j i x hj hi).differentiableAt (by norm_num))
      (P.inverse_germ i j x hi hj) (P.inverse i j x hi hj) k).symm

/-- The chart-independent higher transgression integrand. -/
def tracePowerPrimitiveSection (k : ℕ) (x : E) :
    E [⋀^Fin (1 + powerDegree k)]→L[ℝ] B :=
  let i := Classical.choose (P.cover.exists_mem x)
  traceConnectionCurvaturePower τ.T (D.Γ i) (Θ.θ i) k x

theorem tracePowerPrimitiveSection_eq_local (k : ℕ) (x : E) (i : ι)
    (hi : x ∈ P.U i) :
    tracePowerPrimitiveSection P D Θ τ k x =
      traceConnectionCurvaturePower τ.T (D.Γ i) (Θ.θ i) k x := by
  unfold tracePowerPrimitiveSection
  exact tracePowerPrimitive_transition P D Θ τ k _ i x
    (Classical.choose_spec (P.cover.exists_mem x)) hi

theorem tracePowerPrimitiveSection_germ (k : ℕ) (x : E) (i : ι)
    (hi : x ∈ P.U i) :
    tracePowerPrimitiveSection P D Θ τ k =ᶠ[𝓝 x]
      traceConnectionCurvaturePower τ.T (D.Γ i) (Θ.θ i) k := by
  filter_upwards [((P.U i).isOpen.mem_nhds hi)] with y hy
  exact tracePowerPrimitiveSection_eq_local P D Θ τ k y i hy

/-- The gauge-independent integrand at time `t` along the affine path. -/
def pathTracePowerPrimitiveSection (k : ℕ) (t : ℝ) (x : E) :
    E [⋀^Fin (1 + powerDegree k)]→L[ℝ] B :=
  tracePowerPrimitiveSection P (P.pathConnection D Θ t) Θ τ k x

theorem pathTracePowerPrimitiveSection_eq_local (k : ℕ) (t : ℝ)
    (x : E) (i : ι) (hi : x ∈ P.U i) :
    pathTracePowerPrimitiveSection P D Θ τ k t x =
      traceConnectionCurvaturePower τ.T
        (D.Γ i + t • Θ.θ i) (Θ.θ i) k x :=
  tracePowerPrimitiveSection_eq_local P (P.pathConnection D Θ t) Θ τ k x i hi

/-- The textbook-normalized integrated primitive `(k+2)∫T(θ∧F_t^(k+1))`.
It is an actual differential form on the covered base of the supplied atlas. -/
def integratedTracePowerTransgressionSection [CompleteSpace B]
    (k : ℕ) (x : E) :
    E [⋀^Fin (1 + powerDegree k)]→L[ℝ] B :=
  ((k + 2 : ℕ) : ℝ) •
    ∫ t in (0 : ℝ)..1, pathTracePowerPrimitiveSection P D Θ τ k t x

theorem integratedTracePowerTransgressionSection_germ [CompleteSpace B]
    (k : ℕ) (x : E) (i : ι) (hi : x ∈ P.U i) :
    integratedTracePowerTransgressionSection P D Θ τ k =ᶠ[𝓝 x]
      traceStandardTransgressionForm τ.T (D.Γ i) (Θ.θ i) k := by
  filter_upwards [((P.U i).isOpen.mem_nhds hi)] with y hy
  unfold integratedTracePowerTransgressionSection traceStandardTransgressionForm
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  exact pathTracePowerPrimitiveSection_eq_local P D Θ τ k t y i hy

/-- Every higher curvature trace-power endpoint difference is the exterior
derivative of one chart-independent textbook-normalized transgression form.
The degree cast only identifies propositionally equal finite slot counts. -/
theorem tracePowerSection_sub_eq_extDeriv_standard [CompleteSpace B]
    (k : ℕ)
    (hD2 : ∀ i x, x ∈ P.U i → ContDiffAt ℝ 2 (D.Γ i) x)
    (hΘ2 : ∀ i x, x ∈ P.U i → ContDiffAt ℝ 2 (Θ.θ i) x)
    (x : E) :
    tracePowerSection P (P.pathConnection D Θ 1) τ (k + 1) x -
      tracePowerSection P D τ (k + 1) x =
      traceDegreeCast (primitiveDegree_add_one (k + 1))
        (extDeriv (integratedTracePowerTransgressionSection P D Θ τ k) x) := by
  obtain ⟨i, hi⟩ := P.cover.exists_mem x
  rw [tracePowerSection_eq_local P (P.pathConnection D Θ 1) τ (k + 1) x i hi,
    tracePowerSection_eq_local P D τ (k + 1) x i hi,
    (integratedTracePowerTransgressionSection_germ P D Θ τ k x i hi).extDeriv_eq]
  change tracePowerForm τ.T (D.Γ i + (1 : ℝ) • Θ.θ i) (k + 1) x -
    tracePowerForm τ.T (D.Γ i) (k + 1) x = _
  simpa only [one_smul] using
    (LocalChernWeilStandardExact.tracePowerForm_sub_eq_extDeriv_standard
      τ.T τ.cyclic (D.Γ i) (Θ.θ i) k x
      (hD2 i x hi) (hΘ2 i x hi))

/-- At degree four the descended all-degree integrand is the established
quadratic transgression integrand. -/
theorem tracePowerPrimitiveSection_zero_eq_quadratic :
    tracePowerPrimitiveSection P D Θ τ 0 =
      QuaternionicSymmetry.ProjectiveQuadraticTransgression.transgressionSection
        P D Θ τ := rfl

/-- At degree four the integrated standard primitive agrees with the earlier
quadratic atlas construction, including its factor of two. -/
theorem integratedTracePowerTransgressionSection_zero_eq_quadratic
    [CompleteSpace B] :
    integratedTracePowerTransgressionSection P D Θ τ 0 =
      QuaternionicSymmetry.ProjectiveQuadraticTransgression.integratedTransgressionSection
        P D Θ τ := by
  funext x
  change (2 : ℝ) •
      (∫ t in (0 : ℝ)..1, pathTracePowerPrimitiveSection P D Θ τ 0 t x) =
    ∫ t in (0 : ℝ)..1,
      (2 : ℝ) •
        QuaternionicSymmetry.ProjectiveQuadraticTransgression.pathTransgressionSection
          P D Θ τ t x
  rw [intervalIntegral.integral_smul]
  congr 1

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

local instance : NormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

/-- The atlas endpoint identity with the actual trace of finite-dimensional
real endomorphisms; there is no abstract trace-cyclicity premise. -/
theorem endomorphismTracePowerSection_sub_eq_extDeriv_standard
    (Q : GaugeAtlas ι E (V →L[ℝ] V)) (C : Q.Connection)
    (Ψ : Q.AdjointOneForm) (k : ℕ)
    (hC2 : ∀ i x, x ∈ Q.U i → ContDiffAt ℝ 2 (C.Γ i) x)
    (hΨ2 : ∀ i x, x ∈ Q.U i → ContDiffAt ℝ 2 (Ψ.θ i) x)
    (x : E) :
    tracePowerSection Q (Q.pathConnection C Ψ 1)
        (endomorphismCyclicTrace (V := V)) (k + 1) x -
      tracePowerSection Q C
        (endomorphismCyclicTrace (V := V)) (k + 1) x =
      traceDegreeCast (primitiveDegree_add_one (k + 1))
        (extDeriv (integratedTracePowerTransgressionSection Q C Ψ
          (endomorphismCyclicTrace (V := V)) k) x) :=
  tracePowerSection_sub_eq_extDeriv_standard Q C Ψ
    (endomorphismCyclicTrace (V := V)) k hC2 hΨ2 x

end
end QuaternionicSymmetry.ProjectiveAdjointDescent.GaugeAtlas
