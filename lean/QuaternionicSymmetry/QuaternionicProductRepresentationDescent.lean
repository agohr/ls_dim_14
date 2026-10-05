import QuaternionicSymmetry.QuaternionicNormalizerProductSurjective

/-! Universal descent of any product-group representation whose central
kernel acts trivially through the actual quaternionic normalizer. This is
the algebraic descent mechanism for a future twisted-spinor representation;
no spinor bundle or Dirac operator is postulated here. -/
namespace QuaternionicSymmetry.QuaternionicProductRepresentationDescent
open QuaternionicUnitScalarIsometries
  QuaternionicNormalizerProductSurjective
  QuaternionicIsometryNormalizer
open scoped Quaternion
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
variable (S : QuaternionicStructure E)
variable {H : Type*} [Group H]

def descend (ρ : (symplecticKernel S × unitary ℍ) →* H)
    (hker : ∀ p, symplecticProductAction S p = 1 → ρ p = 1) :
    normalizer S →* H :=
  (symplecticProductAction S).liftOfSurjective
    (symplecticProductAction_surjective S)
    ⟨ρ, by
      intro p hp
      exact hker p (MonoidHom.mem_ker.mp hp)⟩

theorem descend_comp_apply (ρ : (symplecticKernel S × unitary ℍ) →* H)
    (hker : ∀ p, symplecticProductAction S p = 1 → ρ p = 1)
    (p : symplecticKernel S × unitary ℍ) :
    descend S ρ hker (symplecticProductAction S p) = ρ p := by
  simp [descend]

theorem descend_unique (ρ : (symplecticKernel S × unitary ℍ) →* H)
    (hker : ∀ p, symplecticProductAction S p = 1 → ρ p = 1)
    (φ : normalizer S →* H)
    (hφ : ∀ p, φ (symplecticProductAction S p) = ρ p) :
    φ = descend S ρ hker := by
  apply MonoidHom.ext
  intro g
  obtain ⟨p, rfl⟩ := symplecticProductAction_surjective S g
  rw [hφ, descend_comp_apply]

end
end QuaternionicSymmetry.QuaternionicProductRepresentationDescent
