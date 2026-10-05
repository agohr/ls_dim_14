import QuaternionicSymmetry.ComplexProjectiveDiagonalAction
import QuaternionicSymmetry.ComplexTorusCompactKernelDetection

/-! Faithfulness of a diagonal integral complex-torus action on any set of
actual projective points is detected on the compact torus. The set need not
be the whole projective space, span it, or be assumed algebraic. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalKernelDetection

open ComplexProjectiveTopology ComplexProjectiveDiagonalAction
open ComplexTorusCompactKernelDetection TorusLaurentRepresentation
open ManifoldQuaternionicTorusAction TorusCharacterInput
open scoped LinearAlgebra.Projectivization
noncomputable section

variable {r d : ℕ}

/-- A diagonal projective fixed point remains fixed after applying any
homomorphism from complex units to the circle to all torus coordinates. -/
theorem projectiveAction_fixed_map_units
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r)
    (f : ℂˣ →* Circle) (x : Space d)
    (h : projectiveAction μ z x = x) :
    projectiveAction μ (compactInclusion r (fun i => f (z i))) x = x := by
  induction x using Projectivization.ind with
  | h v hv =>
    rw [projectiveAction_mk] at h ⊢
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp h
    apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
    refine ⟨Circle.toUnits (f a), ?_⟩
    ext i
    by_cases hi : v i = 0
    · simp [diagonalEquiv_apply, hi]
    · have hai : a = complexWeightCharacter (μ i) z := by
        apply Units.ext
        have hcoord := congrFun ha i
        change (a : ℂ) * v i = (complexWeightCharacter (μ i) z : ℂ) * v i at hcoord
        exact mul_right_cancel₀ hi hcoord
      simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, diagonalEquiv_apply,
        complexWeightCharacter_compact, weightCharacter_map_units, ← hai]

theorem complex_pointwise_kernel_trivial_of_compact
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hCompact : ∀ t : Torus r,
      (∀ x ∈ A, projectiveAction μ (compactInclusion r t) x = x) → t = 1)
    (z : ComplexTorus r) (hz : ∀ x ∈ A, projectiveAction μ z x = x) :
    z = 1 := by
  have hmod (s : ℝ) : (fun j => modulusCircle s (z j)) = (1 : Torus r) := by
    apply hCompact
    intro x hx
    exact projectiveAction_fixed_map_units μ z (modulusCircle s) x (hz x hx)
  have hnorm (j : Fin r) : ‖(z j : ℂ)‖ = 1 :=
    norm_eq_one_of_modulusCircle (z j) (fun s => congrFun (hmod s) j)
  let t : Torus r := fun j => ⟨(z j : ℂ), by
    change (z j : ℂ) ∈ Metric.sphere 0 1
    simpa only [mem_sphere_zero_iff_norm] using hnorm j⟩
  have ht : compactInclusion r t = z := by
    funext j
    apply Units.ext
    rfl
  have ht1 : t = 1 := hCompact t (by simpa only [ht] using hz)
  rw [← ht, ht1, map_one]

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalKernelDetection
