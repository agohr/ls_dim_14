import QuaternionicSymmetry.LocalChernWeilOrderedExact
import QuaternionicSymmetry.LocalChernWeilOrderedNormalization

/-!
# Standard local Chern--Weil transgression in all higher degrees

The cyclic normalization of the ordered primitive identifies its integral
with the textbook's `j · ∫ tr(θ ∧ F_t^(j-1))` for every `j ≥ 2`.
-/

namespace QuaternionicSymmetry.LocalChernWeilStandardExact

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalChernWeilPowerTransgressionForm
  QuaternionicSymmetry.LocalChernWeilOrderedTransgression
  QuaternionicSymmetry.LocalChernWeilOrderedExact
  QuaternionicSymmetry.LocalChernWeilOrderedNormalization
  QuaternionicSymmetry.LocalChernWeilCubicForm

noncomputable section
open scoped Topology

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

/-- The normalized textbook primitive for the `(k+2)`-nd positive trace
power: `(k+2) ∫ tr(θ ∧ F_t^(k+1)) dt`. -/
def traceStandardTransgressionForm [CompleteSpace B]
    (T : R →L[ℝ] B) (Γ θ : Form (E := E) (A := R)) (k : ℕ) :
    E → E [⋀^Fin (1 + powerDegree k)]→L[ℝ] B := fun y =>
  ((k + 2 : ℕ) : ℝ) •
    ∫ t in (0 : ℝ)..1, traceConnectionCurvaturePower T (Γ + t • θ) θ k y

theorem traceOrderedTransgressionForm_succ_eq_standard [CompleteSpace B]
    (T : R →L[ℝ] B) (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ θ : Form (E := E) (A := R)) (k : ℕ) :
    traceOrderedTransgressionForm T Γ θ (k + 1) =
      traceStandardTransgressionForm T Γ θ k := by
  funext y
  change (∫ t in (0 : ℝ)..1,
      T.compContinuousAlternatingMap
        (orderedPrimitive (Γ + t • θ) θ (k + 1) y)) =
    ((k + 2 : ℕ) : ℝ) •
      ∫ t in (0 : ℝ)..1,
        traceConnectionCurvaturePower T (Γ + t • θ) θ k y
  calc
    (∫ t in (0 : ℝ)..1,
        T.compContinuousAlternatingMap
          (orderedPrimitive (Γ + t • θ) θ (k + 1) y)) =
      ∫ t in (0 : ℝ)..1,
        ((k + 2 : ℕ) : ℝ) •
          traceConnectionCurvaturePower T (Γ + t • θ) θ k y := by
            apply intervalIntegral.integral_congr
            intro t _
            exact trace_orderedPrimitive_succ T hT (Γ + t • θ) θ y k
    _ = ((k + 2 : ℕ) : ℝ) •
        ∫ t in (0 : ℝ)..1,
          traceConnectionCurvaturePower T (Γ + t • θ) θ k y := by
            rw [intervalIntegral.integral_smul]

/-- The standard normalized degree-`j` local transgression for `j=k+2`.
The equality is between actual continuous alternating forms at a point. -/
theorem tracePowerForm_sub_eq_extDeriv_standard [CompleteSpace B]
    (T : R →L[ℝ] B) (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ θ : Form (E := E) (A := R)) (k : ℕ) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x) :
    tracePowerForm T (Γ + θ) (k + 1) x -
      tracePowerForm T Γ (k + 1) x =
      traceDegreeCast (primitiveDegree_add_one (k + 1))
        (extDeriv (traceStandardTransgressionForm T Γ θ k) x) := by
  rw [← traceOrderedTransgressionForm_succ_eq_standard T hT Γ θ k]
  exact tracePowerForm_sub_eq_extDeriv_ordered T hT Γ θ (k + 1) x hΓ hθ

/-- Concrete cubic six-form endpoint with its standard factor-three primitive. -/
theorem traceCubeForm_sub_eq_extDeriv_standard [CompleteSpace B]
    (T : R →L[ℝ] B) (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x) :
    traceCubeForm T (Γ + θ) x - traceCubeForm T Γ x =
      traceDegreeCast (primitiveDegree_add_one 2)
        (extDeriv (traceStandardTransgressionForm T Γ θ 1) x) := by
  have h := tracePowerForm_sub_eq_extDeriv_standard T hT Γ θ 1 x hΓ hθ
  have heq₁ := congrArg (fun φ : E → E [⋀^Fin 6]→L[ℝ] B => φ x)
    (tracePowerForm_two_eq_traceCubeForm T (Γ + θ))
  have heq₀ := congrArg (fun φ : E → E [⋀^Fin 6]→L[ℝ] B => φ x)
    (tracePowerForm_two_eq_traceCubeForm T Γ)
  change tracePowerForm T (Γ + θ) 2 x = traceCubeForm T (Γ + θ) x at heq₁
  change tracePowerForm T Γ 2 x = traceCubeForm T Γ x at heq₀
  change tracePowerForm T (Γ + θ) 2 x - tracePowerForm T Γ 2 x = _ at h
  rw [heq₁, heq₀] at h
  exact h

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

local instance : NormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

/-- Standard transgression with the actual finite-dimensional real trace. -/
theorem traceCurvaturePowerForm_sub_eq_extDeriv_standard
    (Γ θ : Form (E := E) (A := V →L[ℝ] V)) (k : ℕ) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x) :
    traceCurvaturePowerForm (Γ + θ) (k + 1) x -
      traceCurvaturePowerForm Γ (k + 1) x =
      traceDegreeCast (primitiveDegree_add_one (k + 1))
        (extDeriv (traceStandardTransgressionForm
          LocalEndomorphismTrace.traceCLM Γ θ k) x) :=
  tracePowerForm_sub_eq_extDeriv_standard
    LocalEndomorphismTrace.traceCLM
    LocalEndomorphismTrace.traceCLM_cyclic Γ θ k x hΓ hθ

end
end QuaternionicSymmetry.LocalChernWeilStandardExact
