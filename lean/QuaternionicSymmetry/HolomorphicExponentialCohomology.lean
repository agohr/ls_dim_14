import QuaternionicSymmetry.AbelianSheafCohomology
import QuaternionicSymmetry.HolomorphicConstantExponentialSequence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! The boundary map of the proved exponential sequence acts on Mathlib's
actual derived sheaf cohomology. If the adjacent holomorphic-function
cohomology groups vanish, it is an additive equivalence. The vanishing
and the bundle-class/H¹(unit) comparison are not assumed implicitly. -/

namespace QuaternionicSymmetry.HolomorphicExponentialCohomology

open CategoryTheory CategoryTheory.Abelian TopologicalSpace Manifold
open AbelianSheafCohomology HolomorphicUnitSheaf
open HolomorphicConstantExponentialSequence
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

abbrev functionCohomology (n : ℕ) : Type 1 :=
  cohomology B (functionSheaf (B := B) IB) n

abbrev unitCohomology (n : ℕ) : Type 1 :=
  cohomology B (unitSheaf (B := B) IB) n

abbrev integralCohomology (n : ℕ) : Type 1 :=
  cohomology B (integralSheaf B) n

/-- The actual connecting homomorphism, obtained by Yoneda composition
with the extension class of the proved exponential short exact sequence. -/
def exponentialBoundary (n : ℕ) :
    unitCohomology (B := B) IB n →+ integralCohomology (B := B) (n + 1) :=
  (constantExponentialComplex_shortExact (B := B) IB).extClass.postcomp
    (integralSheaf B) rfl

theorem exponentialBoundary_injective (n : ℕ)
    (hvan : Subsingleton (functionCohomology (B := B) IB n)) :
    Function.Injective (exponentialBoundary (B := B) IB n) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃
    (X := integralSheaf B) (constantExponentialComplex_shortExact IB) x rfl hx
  have hy0 : y = 0 := hvan.elim y 0
  rw [hy0, Ext.zero_comp] at hy
  exact hy.symm

theorem exponentialBoundary_surjective (n : ℕ)
    (hvan : Subsingleton (functionCohomology (B := B) IB (n + 1))) :
    Function.Surjective (exponentialBoundary (B := B) IB n) := by
  intro x
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
    (X := integralSheaf B) (constantExponentialComplex_shortExact IB) x
    (hvan.elim _ 0) (n₀ := n) rfl
  exact ⟨y, hy⟩

/-- In particular, the standard `H¹(O*) ≃ H²(ℤ)` deduction uses the
genuine exponential boundary, with its two vanishing hypotheses explicit. -/
def exponentialCohomologyEquiv (n : ℕ)
    (hvan₀ : Subsingleton (functionCohomology (B := B) IB n))
    (hvan₁ : Subsingleton (functionCohomology (B := B) IB (n + 1))) :
    unitCohomology (B := B) IB n ≃+ integralCohomology (B := B) (n + 1) :=
  AddEquiv.ofBijective (exponentialBoundary IB n)
    ⟨exponentialBoundary_injective IB n hvan₀,
      exponentialBoundary_surjective IB n hvan₁⟩

theorem exponentialCohomologyEquiv_apply (n : ℕ)
    (hvan₀ : Subsingleton (functionCohomology (B := B) IB n))
    (hvan₁ : Subsingleton (functionCohomology (B := B) IB (n + 1)))
    (x : unitCohomology (B := B) IB n) :
    exponentialCohomologyEquiv IB n hvan₀ hvan₁ x =
      exponentialBoundary IB n x := rfl

end
end QuaternionicSymmetry.HolomorphicExponentialCohomology
