import QuaternionicSymmetry.CompactTorusEigenbasisSource

/-! Explicit Laurent-monomial extension of integral-weight representations.
This constructs and verifies the representation on complex-torus points.
Preservation of a projective subvariety and an algebraic action on a
manifold are separate geometric obligations, not conclusions of this file. -/
namespace QuaternionicSymmetry.TorusLaurentRepresentation

open ManifoldQuaternionicTorusAction CompactTorusEigenbasisSource
open TorusCharacterInput
open scoped BigOperators
noncomputable section

abbrev ComplexTorus (r : ℕ) := Fin r → ℂˣ

def compactInclusion (r : ℕ) : Torus r →* ComplexTorus r where
  toFun t i := Circle.toUnits (t i)
  map_one' := by funext i; simp
  map_mul' t s := by funext i; simp

def complexWeightCharacter {r : ℕ} (μ : Fin r → ℤ) :
    ComplexTorus r →* ℂˣ where
  toFun z := ∏ i : Fin r, z i ^ μ i
  map_one' := by simp
  map_mul' z w := by simp [mul_zpow, Finset.prod_mul_distrib]

theorem complexWeightCharacter_compact {r : ℕ} (μ : Fin r → ℤ) (t : Torus r) :
    complexWeightCharacter μ (compactInclusion r t) =
      Circle.toUnits (weightCharacter μ t) := by
  change (∏ i : Fin r, Circle.toUnits (t i) ^ μ i) =
    Circle.toUnits (∏ i : Fin r, t i ^ μ i)
  simp only [map_prod, map_zpow]

variable {ι V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Diagonal extension in an actual basis, not a representation on a
replacement vector space. Its coefficients are explicit integral monomials. -/
def complexRepresentation {r : ℕ} (b : Module.Basis ι ℂ V)
    (μ : ι → Fin r → ℤ) : ComplexTorus r →* Module.End ℂ V where
  toFun z := b.constr ℂ (fun i => (complexWeightCharacter (μ i) z : ℂ) • b i)
  map_one' := by
    apply b.ext
    intro i
    simp
  map_mul' z w := by
    apply b.ext
    intro i
    simp [Module.End.mul_apply, smul_smul, mul_comm]

@[simp] theorem complexRepresentation_basis {r : ℕ} (b : Module.Basis ι ℂ V)
    (μ : ι → Fin r → ℤ) (z : ComplexTorus r) (i : ι) :
    complexRepresentation b μ z (b i) = (complexWeightCharacter (μ i) z : ℂ) • b i :=
  b.constr_basis ℂ _ i

theorem complexRepresentation_restrict {r : ℕ} (b : Module.Basis ι ℂ V)
    (μ : ι → Fin r → ℤ) (ρ : Torus r →* Module.End ℂ V)
    (hρ : ∀ t i, ρ t (b i) = (weightCharacter (μ i) t : ℂ) • b i)
    (t : Torus r) :
    complexRepresentation b μ (compactInclusion r t) = ρ t := by
  apply b.ext
  intro i
  rw [complexRepresentation_basis, complexWeightCharacter_compact, hρ]
  rfl

/-- The existing compact representation is recovered exactly by restriction.
Only the eigenbasis and circle-character statements are sourced; the
complex-torus monomials, group laws and restriction equality are internal. -/
theorem exists_laurent_extension
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    {r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (ρ : Torus r →* Module.End ℂ W)
    (hρ : Continuous (fun p : Torus r × W => ρ p.1 p.2)) :
    ∃ b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W,
      ∃ μ : Fin (Module.finrank ℂ W) → (Fin r → ℤ),
        ∀ t : Torus r, complexRepresentation b μ (compactInclusion r t) = ρ t := by
  obtain ⟨b,μ,hμ⟩ := exists_integral_eigenbasis hEigen hCircle ρ hρ
  exact ⟨b,μ,complexRepresentation_restrict b μ ρ hμ⟩

end
end QuaternionicSymmetry.TorusLaurentRepresentation
