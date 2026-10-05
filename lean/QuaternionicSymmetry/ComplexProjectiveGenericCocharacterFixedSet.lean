import QuaternionicSymmetry.TorusIntegralCocharacterPowerSeparation
import QuaternionicSymmetry.TorusIntegralGenericCocharacter

/-! A separating integral one-parameter subgroup has exactly the same
fixed points as the full diagonal complex torus on genuine finite
projective space. This is a coordinate calculation; it assumes no Fano,
Picard, source/attracting-cell, or action-algebraicity conclusion. -/

namespace QuaternionicSymmetry.ComplexProjectiveGenericCocharacterFixedSet

open ComplexProjectiveTopology ComplexProjectiveDiagonalAction
open ComplexProjectiveCocharacterLimit
open TorusLaurentRepresentation TorusIntegralCocharacter
open TorusIntegralGenericCocharacter
open TorusIntegralCocharacterPowerSeparation
open scoped LinearAlgebra.Projectivization
noncomputable section

variable {r d : ℕ}

private theorem pairing_eq_of_projective_fixed
    (μ : Fin (d + 1) → Fin r → ℤ) (u : Fin r → ℤ)
    (v : Coord d) (hv : v ≠ 0)
    (hfix : projectiveAction μ (cocharacter u twoUnit)
      (Projectivization.mk ℂ v hv) = Projectivization.mk ℂ v hv)
    {i j : Fin (d + 1)} (hi : v i ≠ 0) (hj : v j ≠ 0) :
    pairing (μ i) u = pairing (μ j) u := by
  rw [projectiveAction_mk] at hfix
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp hfix
  have hweight (k : Fin (d + 1)) (hk : v k ≠ 0) :
      a = complexWeightCharacter (μ k) (cocharacter u twoUnit) := by
    apply Units.ext
    have hkcoord := congrFun ha k
    change (a : ℂ) * v k =
      (complexWeightCharacter (μ k) (cocharacter u twoUnit) : ℂ) * v k at hkcoord
    exact mul_right_cancel₀ hk hkcoord
  have hchars : complexWeightCharacter (μ i) (cocharacter u twoUnit) =
      complexWeightCharacter (μ j) (cocharacter u twoUnit) :=
    (hweight i hi).symm.trans (hweight j hj)
  rw [character_cocharacter, character_cocharacter] at hchars
  exact twoUnit_zpow_injective hchars

/-- A single generic cocharacter tests the full-torus projective fixed
set: projective support coordinates can be nonzero only in one common
integral-weight block. -/
theorem fixed_full_of_fixed_generic_cocharacter
    (μ : Fin (d + 1) → Fin r → ℤ) (u : Fin r → ℤ)
    (hsep : ∀ i j, pairing (μ i) u = pairing (μ j) u → μ i = μ j)
    (x : Space d)
    (hfix : ∀ z : ℂˣ, projectiveAction μ (cocharacter u z) x = x) :
    ∀ t : ComplexTorus r, projectiveAction μ t x = x := by
  induction x using Projectivization.ind with
  | h v hv =>
    have ⟨i,hi⟩ : ∃ i : Fin (d + 1), v i ≠ 0 := by
      by_contra h
      push_neg at h
      apply hv
      funext j
      exact h j
    intro t
    rw [projectiveAction_mk]
    apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
    refine ⟨complexWeightCharacter (μ i) t, ?_⟩
    ext j
    by_cases hj : v j = 0
    · simp [diagonalEquiv_apply, Units.smul_def, hj]
    · have hpair := pairing_eq_of_projective_fixed μ u v hv
        (hfix twoUnit) hi hj
      have hμ : μ j = μ i := hsep j i hpair.symm
      simp [diagonalEquiv_apply, Units.smul_def, hμ]

theorem fixed_generic_cocharacter_iff_fixed_full
    (μ : Fin (d + 1) → Fin r → ℤ) (u : Fin r → ℤ)
    (hsep : ∀ i j, pairing (μ i) u = pairing (μ j) u → μ i = μ j)
    (x : Space d) :
    (∀ z : ℂˣ, projectiveAction μ (cocharacter u z) x = x) ↔
      (∀ t : ComplexTorus r, projectiveAction μ t x = x) := by
  constructor
  · exact fixed_full_of_fixed_generic_cocharacter μ u hsep x
  · intro h z
    exact h (cocharacter u z)

/-- For every finite integral coordinate-weight family, a genuine
integer cocharacter gives equality of projective fixed sets, not merely
containment or equality of weight values. -/
theorem exists_cocharacter_same_fixed_set
    (μ : Fin (d + 1) → Fin r → ℤ) :
    ∃ u : Fin r → ℤ,
      {x : Space d | ∀ z : ℂˣ,
        projectiveAction μ (cocharacter u z) x = x} =
      {x : Space d | ∀ t : ComplexTorus r,
        projectiveAction μ t x = x} := by
  obtain ⟨u,hu⟩ := exists_separating_cocharacter μ
  refine ⟨u,?_⟩
  ext x
  exact fixed_generic_cocharacter_iff_fixed_full μ u hu x

end
end QuaternionicSymmetry.ComplexProjectiveGenericCocharacterFixedSet
