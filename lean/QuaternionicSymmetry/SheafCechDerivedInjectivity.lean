import QuaternionicSymmetry.SheafCechExtensionMapComparison
import QuaternionicSymmetry.DerivedExtensionClassFaithful
import QuaternionicSymmetry.SheafCechCommonRefinement

/-! Two actual Čech cocycles have the same genuine derived H¹ class
exactly when their actual common-cover sections admit a coboundary
comparison. Both implications are proved through actual extensions. -/

namespace QuaternionicSymmetry.SheafCechDerivedInjectivity

open CategoryTheory TopologicalSpace
open SheafCechOneCocycle SheafCechExtension SheafCechCocycleComparison
open SheafCechExtensionMapComparison DerivedExtensionClassFaithful
open SheafCechCommonRefinement
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι κ : Type}
  {A : TopCat.Sheaf AddCommGrpCat (TopCat.of B)}
  {U : ι → Opens B} {V : κ → Opens B}
  (c : OneCocycle A U) (d : OneCocycle A V)
  (hc : ∀ x : B, ∃ i, x ∈ U i) (hd : ∀ x : B, ∃ a, x ∈ V a)

theorem cohomologyClass_eq_iff_comparison :
    cohomologyClass c hc = cohomologyClass d hd ↔ Nonempty (Comparison c d) := by
  constructor
  · intro h
    obtain ⟨k, hkf, hkg⟩ := (extClass_eq_iff_middle_map
      (extensionComplex c).f (extensionComplex c).g (extensionComplex c).zero
      (extensionComplex d).f (extensionComplex d).g (extensionComplex d).zero
      (extensionComplex_shortExact c hc) (extensionComplex_shortExact d hd)).mp h
    exact ⟨comparison c d hd k hkg hkf⟩
  · rintro ⟨e⟩
    exact cohomologyClass_comparison e hc hd

end
end QuaternionicSymmetry.SheafCechDerivedInjectivity
