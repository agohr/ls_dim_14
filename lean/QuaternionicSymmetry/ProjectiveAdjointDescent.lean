import QuaternionicSymmetry.LocalProjectiveGauge
import QuaternionicSymmetry.LocalChernWeilQuadraticGauge
import Mathlib.Topology.Sets.OpenCover

/-! Algebraic descent of curvature through an indexed projective gauge atlas.

The atlas consists of an actual open cover and smooth local gauge lifts.  Its
triple products need agree only up to a locally fixed simultaneous central
sign.  We construct the associated adjoint fiber at every point as a quotient
of chart values and glue local curvature two-forms into a chart-independent
fiber-valued section.  Constructing the quaternionic frame atlas from a PQK
manifold, and giving these quotient fibers a smooth bundle structure, remain
separate geometric steps. -/

namespace QuaternionicSymmetry.ProjectiveAdjointDescent

open LocalConnection LocalConnectionGauge LocalConnectionForms LocalProjectiveGauge
  LocalChernWeilQuadratic LocalChernWeilQuadraticGauge
open TopologicalSpace
open scoped Topology

noncomputable section

variable {ι E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

local instance : NormedSpace ℝ A := NormedAlgebra.toNormedSpace A

/-- An indexed open cover with local gauge lifts whose triple products form a
projective cocycle.  Inverses and second-order regularity are imposed on actual
overlaps; no global bundle is assumed. -/
structure GaugeAtlas (ι E A : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing A] [NormedAlgebra ℝ A] where
  U : ι → Opens E
  cover : TopologicalSpace.IsOpenCover U
  g : ι → ι → E → A
  diag : ∀ i x, x ∈ U i → g i i x = 1
  inverse : ∀ i j x, x ∈ U i → x ∈ U j → g i j x * g j i x = 1
  regular : ∀ i j x, x ∈ U i → x ∈ U j → ContDiffAt ℝ 2 (g i j) x
  cocycle : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k →
    SignedTransitionGerm (fun y => g i j y * g j k y)
      (fun y => g k j y * g j i y) (g i k) (g k i) x

namespace GaugeAtlas

variable (P : GaugeAtlas ι E A)

/-- A chart value over `x`, before projective adjoint identification. -/
abbrev ChartValue (x : E) := (Σ _ : {i : ι // x ∈ P.U i}, A)

/-- The adjoint coordinate change between two chart values. -/
def Related (x : E) (p q : P.ChartValue x) : Prop :=
  q.2 = P.g q.1.1 p.1.1 x * p.2 * P.g p.1.1 q.1.1 x

theorem related_refl (x : E) (p : P.ChartValue x) : P.Related x p p := by
  rcases p with ⟨⟨i, hi⟩, a⟩
  change a = P.g i i x * a * P.g i i x
  rw [P.diag i x hi]
  simp

theorem related_symm (x : E) (p q : P.ChartValue x)
    (hpq : P.Related x p q) : P.Related x q p := by
  rcases p with ⟨⟨i, hi⟩, a⟩
  rcases q with ⟨⟨j, hj⟩, b⟩
  change b = P.g j i x * a * P.g i j x at hpq
  change a = P.g i j x * b * P.g j i x
  rw [hpq]
  have hinv := P.inverse i j x hi hj
  calc
    a = (P.g i j x * P.g j i x) * a * (P.g i j x * P.g j i x) := by
      rw [hinv]
      simp
    _ = P.g i j x * (P.g j i x * a * P.g i j x) * P.g j i x := by
      noncomm_ring

theorem related_trans (x : E) (p q r : P.ChartValue x)
    (hpq : P.Related x p q) (hqr : P.Related x q r) : P.Related x p r := by
  rcases p with ⟨⟨i, hi⟩, a⟩
  rcases q with ⟨⟨j, hj⟩, b⟩
  rcases r with ⟨⟨k, hk⟩, c⟩
  change b = P.g j i x * a * P.g i j x at hpq
  change c = P.g k j x * b * P.g j k x at hqr
  change c = P.g k i x * a * P.g i k x
  have hproduct : c = (P.g k j x * P.g j i x) * a *
      (P.g i j x * P.g j k x) := by
    rw [hqr, hpq]
    noncomm_ring
  rcases P.cocycle i j k x hi hj hk with ⟨hg, hh⟩ | ⟨hg, hh⟩
  · rw [hh.eq_of_nhds, hg.eq_of_nhds] at hproduct
    exact hproduct
  · rw [hh.eq_of_nhds, hg.eq_of_nhds] at hproduct
    rw [hproduct]
    simp only [Pi.neg_apply, neg_mul, mul_neg, neg_neg]

def chartSetoid (x : E) : Setoid (P.ChartValue x) where
  r := P.Related x
  iseqv := ⟨fun p => P.related_refl x p,
    fun {_ _} hpq => P.related_symm x _ _ hpq,
    fun {_ _ _} hpq hqr => P.related_trans x _ _ _ hpq hqr⟩

/-- The globally defined adjoint fiber obtained from all local chart fibers. -/
def AdjointFiber (x : E) := Quotient (P.chartSetoid x)

def classOf (x : E) (i : ι) (hi : x ∈ P.U i) (a : A) : P.AdjointFiber x :=
  Quotient.mk (P.chartSetoid x) ⟨⟨i, hi⟩, a⟩

theorem classOf_eq_of_transition (x : E) (i j : ι)
    (hi : x ∈ P.U i) (hj : x ∈ P.U j) (a b : A)
    (h : b = P.g j i x * a * P.g i j x) :
    P.classOf x i hi a = P.classOf x j hj b := by
  apply Quotient.sound
  exact h

/-- Local connection forms on this atlas, with the actual gauge law on
overlaps.  These are inputs to descent, not a postulated global connection. -/
structure Connection where
  Γ : ι → Form (E := E) (A := A)
  regular : ∀ i x, x ∈ P.U i → DifferentiableAt ℝ (Γ i) x
  patch : ∀ i j x, x ∈ P.U i → x ∈ P.U j →
    Γ j =ᶠ[𝓝 x] transform (Γ i) (P.g i j) (P.g j i)

/-- An adjoint-valued local one-form, such as the scaled solder form, with
its homogeneous transition law on the same atlas. -/
structure AdjointOneForm where
  θ : ι → Form (E := E) (A := A)
  regular : ∀ i x, x ∈ P.U i → DifferentiableAt ℝ (θ i) x
  patch : ∀ i j x, x ∈ P.U i → x ∈ P.U j →
    θ j =ᶠ[𝓝 x] adjointForm (θ i) (P.g i j) (P.g j i)

variable (D : P.Connection)

/-- The full affine connection path glues under the projective gauge laws. -/
def pathConnection (Θ : P.AdjointOneForm) (t : ℝ) : P.Connection where
  Γ i := D.Γ i + t • Θ.θ i
  regular i x hx := (D.regular i x hx).add ((Θ.regular i x hx).const_smul t)
  patch i j x hi hj := path_transition (D.Γ i) (D.Γ j) (Θ.θ i) (Θ.θ j)
    (P.g i j) (P.g j i) x t (D.patch i j x hi hj) (Θ.patch i j x hi hj)

theorem inverse_germ (i j : ι) (x : E) (hi : x ∈ P.U i) (hj : x ∈ P.U j) :
    (fun y => P.g j i y * P.g i j y) =ᶠ[𝓝 x] fun _ => 1 := by
  filter_upwards [((P.U i).isOpen.mem_nhds hi),
    ((P.U j).isOpen.mem_nhds hj)] with y hyi hyj
  exact P.inverse j i y hyj hyi

/-- The local curvature forms satisfy exactly the adjoint coordinate law. -/
theorem curvature_transition (i j : ι) (x : E)
    (hi : x ∈ P.U i) (hj : x ∈ P.U j) (v : Fin 2 → E) :
    curvatureForm (D.Γ j) x v = P.g j i x * curvatureForm (D.Γ i) x v *
      P.g i j x := by
  exact curvatureForm_transition (D.Γ i) (D.Γ j) (P.g i j) (P.g j i) x
    (D.patch i j x hi hj) (D.regular i x hi) (P.regular i j x hi hj)
    ((P.regular j i x hj hi).differentiableAt (by norm_num))
    (P.inverse_germ i j x hi hj) (P.inverse i j x hi hj) v

def localCurvatureClass (x : E) (i : ι) (hi : x ∈ P.U i)
    (v : Fin 2 → E) : P.AdjointFiber x :=
  P.classOf x i hi (curvatureForm (D.Γ i) x v)

theorem localCurvatureClass_eq (x : E) (i j : ι)
    (hi : x ∈ P.U i) (hj : x ∈ P.U j) (v : Fin 2 → E) :
    localCurvatureClass P D x i hi v = localCurvatureClass P D x j hj v := by
  exact P.classOf_eq_of_transition x i j hi hj _ _
    (curvature_transition P D i j x hi hj v)

/-- A chart-independent section of the projective adjoint fibers. -/
def curvatureSection (x : E) (v : Fin 2 → E) : P.AdjointFiber x :=
  let i := Classical.choose (P.cover.exists_mem x)
  localCurvatureClass P D x i (Classical.choose_spec (P.cover.exists_mem x)) v

theorem curvatureSection_eq_local (x : E) (i : ι) (hi : x ∈ P.U i)
    (v : Fin 2 → E) :
    curvatureSection P D x v = localCurvatureClass P D x i hi v := by
  unfold curvatureSection
  exact localCurvatureClass_eq P D x _ i
    (Classical.choose_spec (P.cover.exists_mem x)) hi v

/-- Curvature of the glued connection path, valued in the adjoint fiber. -/
def pathCurvatureSection (Θ : P.AdjointOneForm) (t : ℝ) (x : E)
    (v : Fin 2 → E) : P.AdjointFiber x :=
  curvatureSection P (pathConnection P D Θ t) x v

theorem pathCurvatureSection_eq_local (Θ : P.AdjointOneForm) (t : ℝ)
    (x : E) (i : ι) (hi : x ∈ P.U i) (v : Fin 2 → E) :
    pathCurvatureSection P D Θ t x v =
      P.classOf x i hi (curvatureForm (D.Γ i + t • Θ.θ i) x v) := by
  exact curvatureSection_eq_local P (pathConnection P D Θ t) x i hi v

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- A continuous linear functional with cyclicity, the exact algebraic input
for projective descent of the quadratic Chern–Weil form. -/
structure CyclicTrace where
  T : A →L[ℝ] B
  cyclic : ∀ a b : A, T (a * b) = T (b * a)

/-- The actual scalar quadratic trace form agrees on any two atlas charts. -/
theorem traceSquare_transition (τ : CyclicTrace (A := A) (B := B))
    (i j : ι) (x : E) (hi : x ∈ P.U i) (hj : x ∈ P.U j) :
    traceSquareForm τ.T (D.Γ i) x = traceSquareForm τ.T (D.Γ j) x := by
  exact (traceSquareForm_transition τ.T τ.cyclic (D.Γ i) (D.Γ j)
    (P.g i j) (P.g j i) x (D.patch i j x hi hj)
    (D.regular i x hi) (P.regular i j x hi hj)
    ((P.regular j i x hj hi).differentiableAt (by norm_num))
    (P.inverse_germ i j x hi hj) (P.inverse i j x hi hj)).symm

/-- A chart-independent scalar degree-four differential form on the covered
base, constructed from local curvature rather than assumed globally. -/
def traceSquareSection (τ : CyclicTrace (A := A) (B := B)) (x : E) :
    E [⋀^Fin 4]→L[ℝ] B :=
  let i := Classical.choose (P.cover.exists_mem x)
  traceSquareForm τ.T (D.Γ i) x

theorem traceSquareSection_eq_local (τ : CyclicTrace (A := A) (B := B))
    (x : E) (i : ι) (hi : x ∈ P.U i) :
    traceSquareSection P D τ x = traceSquareForm τ.T (D.Γ i) x := by
  unfold traceSquareSection
  exact traceSquare_transition P D τ _ i x
    (Classical.choose_spec (P.cover.exists_mem x)) hi

theorem traceSquareSection_germ (τ : CyclicTrace (A := A) (B := B))
    (x : E) (i : ι) (hi : x ∈ P.U i) :
    traceSquareSection P D τ =ᶠ[𝓝 x] traceSquareForm τ.T (D.Γ i) := by
  filter_upwards [((P.U i).isOpen.mem_nhds hi)] with y hy
  exact traceSquareSection_eq_local P D τ y i hy

/-- Local Chern–Weil closure descends to the global scalar form. -/
theorem traceSquareSection_closed (τ : CyclicTrace (A := A) (B := B))
    (hC2 : ∀ i x, x ∈ P.U i → ContDiffAt ℝ 2 (D.Γ i) x)
    (x : E) : extDeriv (traceSquareSection P D τ) x = 0 := by
  obtain ⟨i, hi⟩ := P.cover.exists_mem x
  rw [(traceSquareSection_germ P D τ x i hi).extDeriv_eq]
  exact traceSquareForm_closed τ.T τ.cyclic (D.Γ i) x (hC2 i x hi)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

local instance : NormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

/-- Concrete cyclic trace on finite-dimensional real endomorphisms. -/
def endomorphismCyclicTrace : CyclicTrace (A := V →L[ℝ] V) (B := ℝ) where
  T := LocalEndomorphismTrace.traceCLM
  cyclic := LocalEndomorphismTrace.traceCLM_cyclic

/-- The chart-independent degree-four form obtained from actual endomorphism
trace is closed when the local connections are twice differentiable. -/
theorem endomorphismTraceSquareSection_closed
    (Q : GaugeAtlas ι E (V →L[ℝ] V)) (C : Q.Connection)
    (hC2 : ∀ i x, x ∈ Q.U i → ContDiffAt ℝ 2 (C.Γ i) x)
    (x : E) :
    extDeriv (traceSquareSection Q C (endomorphismCyclicTrace (V := V))) x = 0 :=
  traceSquareSection_closed Q C (endomorphismCyclicTrace (V := V)) hC2 x

end GaugeAtlas
end
end QuaternionicSymmetry.ProjectiveAdjointDescent
