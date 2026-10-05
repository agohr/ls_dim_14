import QuaternionicSymmetry.ComplexAbelianCoefficientAdjunction
import QuaternionicSymmetry.SheafPointwiseAdjunction
import QuaternionicSymmetry.SheafComplexSheafification
import QuaternionicSymmetry.AbelianSheafCohomology
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! Exact complexification and forgetful functors on the actual small sheaf
categories of a topological space. Exactness is constructed internally,
including preservation of colimits by the underlying additive sheaf. -/

namespace QuaternionicSymmetry.ComplexAbelianSheafAdjunction

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open ComplexAbelianCoefficientAdjunction
noncomputable section

variable (X : TopCat.{0})

abbrev topology := Opens.grothendieckTopology X
abbrev additiveSheaves := Sheaf (topology X) AddCommGrpCat.{0}
abbrev complexSheaves := Sheaf (topology X) (ModuleCat.{0} ℂ)

abbrev complexify : additiveSheaves X ⥤ complexSheaves X :=
  Sheaf.composeAndSheafify (topology X) complexification

abbrev forget : complexSheaves X ⥤ additiveSheaves X :=
  sheafCompose (topology X) underlying

abbrev coinduce : additiveSheaves X ⥤ complexSheaves X :=
  sheafCompose (topology X) coinduction

def complexifyAdjunction : complexify X ⊣ forget X :=
  Sheaf.adjunction (topology X) complexificationAdjunction

def forgetAdjunction : forget X ⊣ coinduce X :=
  SheafPointwiseAdjunction.sheafAdjunction (topology X) underlyingAdjunction

instance : (forget X).IsRightAdjoint := (complexifyAdjunction X).isRightAdjoint
instance : (forget X).IsLeftAdjoint := (forgetAdjunction X).isLeftAdjoint
instance : (complexify X).IsLeftAdjoint := (complexifyAdjunction X).isLeftAdjoint

instance : (forget X).Additive where
  map_add := by
    intro P Q f g
    apply Sheaf.Hom.ext
    ext U
    rfl

instance : (complexify X).Additive := (complexifyAdjunction X).left_adjoint_additive

instance : PreservesFiniteLimits (complexify X) := by
  letI : PreservesFiniteLimits
      ((Functor.whiskeringRight (Opens X)ᵒᵖ _ _).obj complexification) :=
    ⟨fun _ _ _ => inferInstance⟩
  letI : PreservesFiniteLimits
      ((Functor.whiskeringRight _ _ _).obj complexification ⋙
        presheafToSheaf (topology X) (ModuleCat.{0} ℂ)) :=
    comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits _ _

end
end QuaternionicSymmetry.ComplexAbelianSheafAdjunction
