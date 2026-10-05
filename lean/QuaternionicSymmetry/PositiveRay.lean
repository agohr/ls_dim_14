import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! A functional criterion for membership in the nonnegative ray generated
by a nonzero vector. No ordering on the ambient vector space is required. -/

namespace QuaternionicSymmetry.PositiveRay

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def Contains (v x : V) : Prop := ∃ r : ℝ, 0 ≤ r ∧ x = r • v

theorem smul {v x : V} (hx : Contains v x) {r : ℝ} (hr : 0 ≤ r) :
    Contains v (r • x) := by
  obtain ⟨s, hs, rfl⟩ := hx
  exact ⟨r * s, mul_nonneg hr hs, smul_smul r s v⟩

theorem functional_nonneg {v x : V} (hx : Contains v x)
    (L : V →ₗ[ℝ] ℝ) (hv : 0 ≤ L v) : 0 ≤ L x := by
  obtain ⟨r, hr, rfl⟩ := hx
  simpa only [map_smul, smul_eq_mul] using mul_nonneg hr hv

theorem contains_iff_functional_nonneg {v x : V} (hv : v ≠ 0) :
    Contains v x ↔ ∀ L : V →ₗ[ℝ] ℝ, 0 ≤ L v → 0 ≤ L x := by
  refine ⟨fun hx L hL => functional_nonneg hx L hL, fun h => ?_⟩
  obtain ⟨L, hL⟩ := Module.Projective.exists_dual_eq_one ℝ hv
  refine ⟨L x, h L (by rw [hL]; norm_num), ?_⟩
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℝ (x - L x • v)).mp
  intro F
  let G : V →ₗ[ℝ] ℝ := F - F v • L
  have hG : G v = 0 := by simp [G, hL]
  have hp : 0 ≤ G x := h G hG.ge
  have hn : 0 ≤ -G x := by
    simpa only [LinearMap.neg_apply] using h (-G) (by simp [hG])
  have hz : G x = 0 := le_antisymm (by linarith) hp
  simpa only [G, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    map_sub, map_smul, mul_comm] using hz

end QuaternionicSymmetry.PositiveRay
