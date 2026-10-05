import QuaternionicSymmetry.AbelianToralRootSpace

/-! A nonzero exact eigenvector inside a generalized root space forces
the root character to take the same value on that generator. This does
not assume the whole adjoint action is diagonalizable. -/

namespace QuaternionicSymmetry.ToralRootEigenvalueUniqueness

open scoped LieAlgebra
noncomputable section

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  (H : LieSubalgebra ℂ L) [LieRing.IsNilpotent H]
  (α : H → ℂ) (s : H) (v : L)

theorem root_value_eq_of_exact_eigenvector
    (hvroot : v ∈ LieAlgebra.rootSpace H α)
    (hvne : v ≠ 0) (c : ℂ)
    (heig : ⁅(s : L),v⁆ = c • v) : α s = c := by
  let f := LieModule.toEnd ℂ H L s
  have hgenα : v ∈ LieModule.genWeightSpaceOf L (α s) s :=
    (LieModule.genWeightSpace_le_genWeightSpaceOf L s α) hvroot
  have hEig : v ∈ f.eigenspace c := by
    rw [Module.End.mem_eigenspace_iff]
    exact heig
  have hgenC : v ∈ LieModule.genWeightSpaceOf L c s := by
    change v ∈ f.maxGenEigenspace c
    exact Module.End.eigenspace_le_maxGenEigenspace hEig
  by_contra hne
  have hdis := LieModule.disjoint_genWeightSpaceOf (R := ℂ) (L := H) (M := L)
    (x := s) (φ₁ := α s) (φ₂ := c) hne
  have hvbot : v ∈ (⊥ : LieSubmodule ℂ H L) := by
    rw [← hdis.eq_bot]
    exact ⟨hgenα,hgenC⟩
  exact hvne (by simpa using hvbot)

end
end QuaternionicSymmetry.ToralRootEigenvalueUniqueness
