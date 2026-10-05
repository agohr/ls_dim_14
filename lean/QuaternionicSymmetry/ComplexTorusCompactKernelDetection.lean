import QuaternionicSymmetry.TorusLaurentRepresentation
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! A family of integral characters with trivial compact-torus kernel also
has trivial complex-torus kernel. The proof detects every modulus using
circle characters of the logarithmic modulus, then uses the compact kernel
once more for the unit-modulus part. No lattice saturation or faithfulness
of complexification is assumed. -/

namespace QuaternionicSymmetry.ComplexTorusCompactKernelDetection

open TorusLaurentRepresentation ManifoldQuaternionicTorusAction TorusCharacterInput
open scoped BigOperators
noncomputable section

/-- Logarithmic modulus followed by any real circle frequency. -/
def modulusCircle (s : ℝ) : ℂˣ →* Circle where
  toFun z := Circle.exp (s * Real.log ‖(z : ℂ)‖)
  map_one' := by simp
  map_mul' z w := by
    simp only [Units.val_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr z.ne_zero) (norm_ne_zero_iff.mpr w.ne_zero),
      mul_add, Circle.exp_add]

theorem weightCharacter_map_units {r : ℕ} (μ : Fin r → ℤ)
    (f : ℂˣ →* Circle) (z : ComplexTorus r) :
    weightCharacter μ (fun i => f (z i)) = f (complexWeightCharacter μ z) := by
  simp [weightCharacter, complexWeightCharacter, map_prod, map_zpow]

/-- All logarithmic-modulus circle frequencies detect whether a unit has
modulus one. The half-turn gives an explicit contradiction otherwise. -/
theorem norm_eq_one_of_modulusCircle (z : ℂˣ)
    (h : ∀ s : ℝ, modulusCircle s z = 1) : ‖(z : ℂ)‖ = 1 := by
  have hlog : Real.log ‖(z : ℂ)‖ = 0 := by
    by_contra hn
    have hp := h (Real.pi / Real.log ‖(z : ℂ)‖)
    change Circle.exp (Real.pi / Real.log ‖(z : ℂ)‖ * Real.log ‖(z : ℂ)‖) = 1 at hp
    rw [div_mul_cancel₀ _ hn] at hp
    exact Circle.exp_pi_ne_one hp
  calc
    ‖(z : ℂ)‖ = Real.exp (Real.log ‖(z : ℂ)‖) :=
      (Real.exp_log (norm_pos_iff.mpr z.ne_zero)).symm
    _ = 1 := by rw [hlog, Real.exp_zero]

theorem complex_kernel_trivial_of_compact {r : ℕ} {ι : Type*}
    (μ : ι → Fin r → ℤ)
    (hCompact : ∀ t : Torus r, (∀ i, weightCharacter (μ i) t = 1) → t = 1)
    (z : ComplexTorus r) (hz : ∀ i, complexWeightCharacter (μ i) z = 1) :
    z = 1 := by
  have hmod (s : ℝ) : (fun j => modulusCircle s (z j)) = (1 : Torus r) := by
    apply hCompact
    intro i
    rw [weightCharacter_map_units, hz, map_one]
  have hnorm (j : Fin r) : ‖(z j : ℂ)‖ = 1 :=
    norm_eq_one_of_modulusCircle (z j) (fun s => congrFun (hmod s) j)
  let t : Torus r := fun j => ⟨(z j : ℂ), by
    change (z j : ℂ) ∈ Metric.sphere 0 1
    simpa only [mem_sphere_zero_iff_norm] using hnorm j⟩
  have ht : compactInclusion r t = z := by
    funext j
    apply Units.ext
    rfl
  have ht1 : t = 1 := by
    apply hCompact
    intro i
    apply Circle.coe_injective
    have hi := congrArg (fun u : ℂˣ => (u : ℂ)) (hz i)
    rw [← ht, complexWeightCharacter_compact] at hi
    exact hi
  rw [← ht, ht1, map_one]

end
end QuaternionicSymmetry.ComplexTorusCompactKernelDetection
