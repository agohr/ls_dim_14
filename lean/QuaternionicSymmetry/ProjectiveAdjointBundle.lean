import QuaternionicSymmetry.ProjectiveAdjointDescent
import Mathlib.Topology.VectorBundle.Basic

/-! A genuine continuous vector bundle from projective gauge transitions.

Conjugation removes the simultaneous central sign in the triple cocycle.  The
resulting continuous linear coordinate changes define a mathlib
`VectorBundleCore`, hence an honest topological vector bundle with proved local
trivializations.  Its fibers are compared below with the chart-value quotient
from `ProjectiveAdjointDescent`.  This construction is still conditional on a
`GaugeAtlas`; the quaternionic frame atlas of a PQK manifold is not yet built. -/

namespace QuaternionicSymmetry.ProjectiveAdjointDescent.GaugeAtlas

open QuaternionicSymmetry.ProjectiveAdjointDescent
open TopologicalSpace
open scoped Topology Bundle

noncomputable section

variable {ι E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

local instance : NormedSpace ℝ A := NormedAlgebra.toNormedSpace A

variable (P : GaugeAtlas ι E A)

/-- Adjoint coordinate change between local fibers, as a continuous linear map. -/
def adjointCoordChange (i j : ι) (x : E) : A →L[ℝ] A :=
  ((ContinuousLinearMap.mul ℝ A) (P.g j i x)).comp
    (((ContinuousLinearMap.mul ℝ A).flip) (P.g i j x))

theorem adjointCoordChange_apply (i j : ι) (x : E) (a : A) :
    P.adjointCoordChange i j x a = P.g j i x * a * P.g i j x := by
  change P.g j i x * (a * P.g i j x) = _
  rw [mul_assoc]

theorem adjointCoordChange_self (i : ι) (x : E) (hx : x ∈ P.U i) (a : A) :
    P.adjointCoordChange i i x a = a := by
  rw [adjointCoordChange_apply, P.diag i x hx]
  simp

theorem adjointCoordChange_comp (i j k : ι) (x : E)
    (hi : x ∈ P.U i) (hj : x ∈ P.U j) (hk : x ∈ P.U k) (a : A) :
    P.adjointCoordChange j k x (P.adjointCoordChange i j x a) =
      P.adjointCoordChange i k x a := by
  have hpq : P.Related x ⟨⟨i, hi⟩, a⟩
      ⟨⟨j, hj⟩, P.adjointCoordChange i j x a⟩ := by
    change P.adjointCoordChange i j x a = P.g j i x * a * P.g i j x
    exact P.adjointCoordChange_apply i j x a
  have hqr : P.Related x ⟨⟨j, hj⟩, P.adjointCoordChange i j x a⟩
      ⟨⟨k, hk⟩, P.adjointCoordChange j k x (P.adjointCoordChange i j x a)⟩ := by
    change P.adjointCoordChange j k x (P.adjointCoordChange i j x a) =
      P.g k j x * P.adjointCoordChange i j x a * P.g j k x
    exact P.adjointCoordChange_apply j k x _
  have hpr := P.related_trans x _ _ _ hpq hqr
  change P.adjointCoordChange j k x (P.adjointCoordChange i j x a) =
    P.g k i x * a * P.g i k x at hpr
  simpa only [adjointCoordChange_apply] using hpr

theorem continuousOn_adjointCoordChange (i j : ι) :
    ContinuousOn (P.adjointCoordChange i j)
      ((P.U i : Set E) ∩ (P.U j : Set E)) := by
  intro x hx
  have hgji : ContinuousAt (P.g j i) x :=
    (P.regular j i x hx.2 hx.1).continuousAt
  have hgij : ContinuousAt (P.g i j) x :=
    (P.regular i j x hx.1 hx.2).continuousAt
  exact (((ContinuousLinearMap.mul ℝ A).continuous.continuousAt.comp hgji).clm_comp
    (((ContinuousLinearMap.mul ℝ A).flip).continuous.continuousAt.comp hgij)).continuousWithinAt

/-- Mathlib's continuous vector-bundle core induced by the projective atlas. -/
def vectorCore : VectorBundleCore ℝ E A ι where
  baseSet i := P.U i
  isOpen_baseSet i := (P.U i).isOpen
  indexAt x := Classical.choose (P.cover.exists_mem x)
  mem_baseSet_at x := Classical.choose_spec (P.cover.exists_mem x)
  coordChange := P.adjointCoordChange
  coordChange_self i x hx a := P.adjointCoordChange_self i x hx a
  continuousOn_coordChange i j := P.continuousOn_adjointCoordChange i j
  coordChange_comp i j k x hx a :=
    P.adjointCoordChange_comp i j k x hx.1.1 hx.1.2 hx.2 a

/-- The resulting actual topological vector-bundle structure, supplied by
mathlib's core-to-bundle construction. -/
def vectorBundleStructure : VectorBundle ℝ A P.vectorCore.Fiber :=
  P.vectorCore.vectorBundle

/-- The local trivialization supplied by mathlib is based exactly on the
corresponding open set of the projective gauge atlas. -/
theorem mem_localTriv_source (i : ι) (x : E) (a : A) :
    (⟨x, a⟩ : P.vectorCore.TotalSpace) ∈ (P.vectorCore.localTriv i).source ↔
      x ∈ P.U i := by
  simpa only [vectorCore] using
    (P.vectorCore.mem_localTriv_source i (⟨x, a⟩ : P.vectorCore.TotalSpace))

/-- The actual bundle-trivialization change is the conjugation prescribed by
the projective gauge lifts. -/
theorem localTriv_coordChange (i j : ι) (x : E)
    (hi : x ∈ P.U i) (hj : x ∈ P.U j) (a : A) :
    (Trivialization.coordChangeL ℝ (P.vectorCore.localTriv i)
      (P.vectorCore.localTriv j) x) a = P.g j i x * a * P.g i j x := by
  have hb : x ∈ (P.vectorCore.localTriv i).baseSet ∧
      x ∈ (P.vectorCore.localTriv j).baseSet := by
    constructor
    · rw [← P.vectorCore.baseSet_at]
      exact hi
    · rw [← P.vectorCore.baseSet_at]
      exact hj
  calc
    _ = P.vectorCore.coordChange i j x a :=
      P.vectorCore.localTriv_coordChange_eq i j hb a
    _ = P.g j i x * a * P.g i j x := P.adjointCoordChange_apply i j x a

/-- Coordinate of a quotient chart value in the canonical trivialization
selected by the open cover at `x`. -/
def toCanonical (x : E) (p : P.ChartValue x) : A :=
  P.adjointCoordChange p.1.1 (P.vectorCore.indexAt x) x p.2

theorem toCanonical_congr (x : E) (p q : P.ChartValue x)
    (hpq : P.Related x p q) : P.toCanonical x p = P.toCanonical x q := by
  rcases p with ⟨⟨i, hi⟩, a⟩
  rcases q with ⟨⟨j, hj⟩, b⟩
  let c := P.vectorCore.indexAt x
  have hc : x ∈ P.U c := P.vectorCore.mem_baseSet_at x
  change b = P.g j i x * a * P.g i j x at hpq
  have hcoord : b = P.adjointCoordChange i j x a := by
    rw [P.adjointCoordChange_apply]
    exact hpq
  change P.adjointCoordChange i c x a = P.adjointCoordChange j c x b
  rw [hcoord]
  exact (P.adjointCoordChange_comp i j c x hi hj hc a).symm

def quotientToCanonical (x : E) : P.AdjointFiber x → A :=
  Quotient.lift (P.toCanonical x) (P.toCanonical_congr x)

/-- The algebraic quotient fiber agrees with the fiber used by mathlib's
continuous vector-bundle core. -/
def fiberEquiv (x : E) : P.AdjointFiber x ≃ A where
  toFun := P.quotientToCanonical x
  invFun a := P.classOf x (P.vectorCore.indexAt x)
    (P.vectorCore.mem_baseSet_at x) a
  left_inv := by
    intro z
    induction z using Quotient.inductionOn with
    | _ p =>
      rcases p with ⟨⟨i, hi⟩, a⟩
      change P.classOf x (P.vectorCore.indexAt x)
        (P.vectorCore.mem_baseSet_at x)
        (P.adjointCoordChange i (P.vectorCore.indexAt x) x a) =
        P.classOf x i hi a
      exact (P.classOf_eq_of_transition x i (P.vectorCore.indexAt x) hi
        (P.vectorCore.mem_baseSet_at x) a _
        (P.adjointCoordChange_apply i (P.vectorCore.indexAt x) x a)).symm
  right_inv := by
    intro a
    change P.adjointCoordChange (P.vectorCore.indexAt x)
      (P.vectorCore.indexAt x) x a = a
    exact P.adjointCoordChange_self (P.vectorCore.indexAt x) x
      (P.vectorCore.mem_baseSet_at x) a

/-- In the canonical bundle coordinate, the descended curvature is the
ordinary local curvature transported from any available chart. -/
theorem curvatureSection_bundle_coordinate (D : P.Connection) (x : E)
    (i : ι) (hi : x ∈ P.U i) (v : Fin 2 → E) :
    P.fiberEquiv x (curvatureSection P D x v) =
      P.adjointCoordChange i (P.vectorCore.indexAt x) x
        (LocalConnectionForms.curvatureForm (D.Γ i) x v) := by
  rw [curvatureSection_eq_local P D x i hi v]
  rfl

end
end QuaternionicSymmetry.ProjectiveAdjointDescent.GaugeAtlas
