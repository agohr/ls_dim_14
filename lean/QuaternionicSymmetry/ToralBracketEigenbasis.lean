import QuaternionicSymmetry.ToralEigenCharacter

/-! A basis of common eigenvectors for toral generators remains a bracket
eigenbasis for their actual complex-span Lie subalgebra. -/

namespace QuaternionicSymmetry.ToralBracketEigenbasis

open AbelianToralRootSpace ToralEigenCharacter
noncomputable section

variable {ι L : Type*} [LieRing L] [LieAlgebra ℂ L]

theorem exists_bracket_eigenbasis
    (S : Set L) (hComm : ∀ x ∈ S, ∀ y ∈ S, ⁅x,y⁆ = 0)
    (b : Module.Basis ι ℂ L)
    (hEig : ∀ i, ∀ s ∈ S, ∃ c : ℂ, ⁅s,b i⁆ = c • b i) :
    ∃ χ : H S hComm → ι → ℂ,
      ∀ (h : H S hComm) i, ⁅(h : L),b i⁆ = χ h i • b i := by
  let χ : H S hComm → ι → ℂ :=
    fun h i => eigenCharacter S hComm (b i) (hEig i) h
  exact ⟨χ, fun h i => bracket_eq_character S hComm (b i) (hEig i) h⟩

end
end QuaternionicSymmetry.ToralBracketEigenbasis
