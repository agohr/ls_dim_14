import QuaternionicSymmetry.ComplexProjectiveGenericCocharacterFixedSet
import QuaternionicSymmetry.TorusWeightSeparation

/-! The compact standard torus and its Laurent complexification have
exactly the same fixed points for an actual diagonal projective action.
The proof checks nonzero projective support coordinates and uses the
already established injectivity of integral circle characters. -/

namespace QuaternionicSymmetry.ComplexProjectiveCompactFullFixedSet

open ComplexProjectiveTopology ComplexProjectiveDiagonalAction
open TorusLaurentRepresentation TorusWeightSeparation
open ManifoldQuaternionicTorusAction
open scoped LinearAlgebra.Projectivization
noncomputable section

variable {r d : ℕ}

/-- A point fixed by every compact torus element is fixed by its full
Laurent complex torus, for the same diagonal coordinate weights. -/
theorem fixed_full_of_fixed_compact
    (μ : Fin (d + 1) → Fin r → ℤ) (x : Space d)
    (hfix : ∀ t : Torus r,
      projectiveAction μ (compactInclusion r t) x = x) :
    ∀ z : ComplexTorus r, projectiveAction μ z x = x := by
  induction x using Projectivization.ind with
  | h v hv =>
    have ⟨i,hi⟩ : ∃ i : Fin (d + 1), v i ≠ 0 := by
      by_contra h
      push_neg at h
      apply hv
      funext j
      exact h j
    have hsupport (j : Fin (d + 1)) (hj : v j ≠ 0) : μ j = μ i := by
      apply weight_eq_of_character_eq
      intro t
      have ht := hfix t
      rw [projectiveAction_mk] at ht
      obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp ht
      have hweight (k : Fin (d + 1)) (hk : v k ≠ 0) :
          a = complexWeightCharacter (μ k) (compactInclusion r t) := by
        apply Units.ext
        have hkcoord := congrFun ha k
        change (a : ℂ) * v k =
          (complexWeightCharacter (μ k) (compactInclusion r t) : ℂ) * v k
          at hkcoord
        exact mul_right_cancel₀ hk hkcoord
      have hc : complexWeightCharacter (μ j) (compactInclusion r t) =
          complexWeightCharacter (μ i) (compactInclusion r t) :=
        (hweight j hj).symm.trans (hweight i hi)
      rw [complexWeightCharacter_compact, complexWeightCharacter_compact] at hc
      apply Subtype.ext
      exact congrArg (fun a : ℂˣ => (a : ℂ)) hc
    intro z
    rw [projectiveAction_mk]
    apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
    refine ⟨complexWeightCharacter (μ i) z, ?_⟩
    ext j
    by_cases hj : v j = 0
    · simp [diagonalEquiv_apply, hj]
    · simp [diagonalEquiv_apply, hsupport j hj, Units.smul_def]

theorem fixed_compact_iff_fixed_full
    (μ : Fin (d + 1) → Fin r → ℤ) (x : Space d) :
    (∀ t : Torus r, projectiveAction μ (compactInclusion r t) x = x) ↔
      (∀ z : ComplexTorus r, projectiveAction μ z x = x) := by
  constructor
  · exact fixed_full_of_fixed_compact μ x
  · intro h t
    exact h (compactInclusion r t)

/-- An actual generic cocharacter has precisely the compact torus's
projective fixed set. Consequently their connected components in any
common invariant projective subspace are the same literal subsets. -/
theorem exists_cocharacter_same_compact_fixed_set
    (μ : Fin (d + 1) → Fin r → ℤ) :
    ∃ u : Fin r → ℤ,
      {x : Space d | ∀ z : ℂˣ,
        projectiveAction μ (TorusIntegralCocharacter.cocharacter u z) x = x} =
      {x : Space d | ∀ t : Torus r,
        projectiveAction μ (compactInclusion r t) x = x} := by
  obtain ⟨u,hu⟩ :=
    ComplexProjectiveGenericCocharacterFixedSet.exists_cocharacter_same_fixed_set μ
  refine ⟨u,?_⟩
  ext x
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
  exact (Set.ext_iff.mp hu x).trans (fixed_compact_iff_fixed_full μ x).symm

end
end QuaternionicSymmetry.ComplexProjectiveCompactFullFixedSet
