import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Tactic

/-!
The elementary linear-algebra part of the hyperholomorphic-form construction.
For a real inner-product space, a skew-adjoint endomorphism determines an
actual alternating two-form.  A linear isometry commuting with the
endomorphism preserves that form.  These statements are purely algebraic and
make no geometric assumptions.
-/

namespace QuaternionicSymmetry.HyperholomorphicForms

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The bilinear expression associated with an endomorphism. -/
def innerEndomorphism (A : V →ₗ[ℝ] V) :
    MultilinearMap ℝ (fun _ : Fin 2 => V) ℝ :=
  MultilinearMap.mk' (fun v => inner ℝ (A (v 0)) (v 1))
    (by
      intro v i x y
      fin_cases i <;>
        simp [Function.update, inner_add_left, inner_add_right, A.map_add])
    (by
      intro v i c x
      fin_cases i <;>
        simp [Function.update, inner_smul_left, inner_smul_right, A.map_smul])

private theorem skew_self_zero (A : V →ₗ[ℝ] V)
    (hskew : ∀ v w : V, inner ℝ (A v) w = -inner ℝ v (A w)) (v : V) :
    inner ℝ (A v) v = 0 := by
  have h := hskew v v
  rw [real_inner_comm] at h
  have hz : inner ℝ v (A v) = 0 := by linarith
  rw [real_inner_comm]
  exact hz

/-- The alternating two-form `θ(v,w) = ⟪A v,w⟫`. -/
def theta (A : V →ₗ[ℝ] V)
    (hskew : ∀ v w : V, inner ℝ (A v) w = -inner ℝ v (A w)) :
    V [⋀^(Fin 2)]→ₗ[ℝ] ℝ :=
  { toMultilinearMap := innerEndomorphism A
    map_eq_zero_of_eq' := by
      intro v i j hij hne
      fin_cases i <;> fin_cases j
      · exact (hne rfl).elim
      · change inner ℝ (A (v 0)) (v 1) = 0
        have hv : v 0 = v 1 := by simpa using hij
        rw [← hv]
        exact skew_self_zero A hskew (v 0)
      · change inner ℝ (A (v 0)) (v 1) = 0
        have hv : v 1 = v 0 := by simpa using hij
        rw [hv]
        exact skew_self_zero A hskew (v 0)
      · exact (hne rfl).elim }

@[simp] theorem theta_apply (A : V →ₗ[ℝ] V)
    (hskew : ∀ v w : V, inner ℝ (A v) w = -inner ℝ v (A w)) (v : Fin 2 → V) :
    theta A hskew v = inner ℝ (A (v 0)) (v 1) := rfl

/-- A commuting linear isometry preserves the two-form associated with `A`. -/
theorem theta_invariant (A : V →ₗ[ℝ] V)
    (hskew : ∀ v w : V, inner ℝ (A v) w = -inner ℝ v (A w))
    (J : V →ₗᵢ[ℝ] V)
    (hcomm : ∀ v : V, A (J v) = J (A v))
    (v : Fin 2 → V) :
    theta A hskew (fun i => J (v i)) = theta A hskew v := by
  simp only [theta_apply]
  rw [hcomm (v 0), J.inner_map_map]

end QuaternionicSymmetry.HyperholomorphicForms
