import QuaternionicSymmetry.LocallyConstantIntegerSheaf
import QuaternionicSymmetry.AbelianSheafCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! The sheaf of actual locally constant integer functions is the genuine
categorical constant integer sheaf: the comparison from constant sections
is locally bijective, including on disconnected and empty open sets. -/

namespace QuaternionicSymmetry.LocallyConstantIntegerSheafComparison

open CategoryTheory TopologicalSpace Opposite
open LocallyConstantIntegerSheaf
noncomputable section

variable (B : Type) [TopologicalSpace B]

def constantSection (U : Opens B) : ℤ →+ (integerSheaf B).val.obj (op U) where
  toFun n := TopCat.ofHom (ContinuousMap.const U n)
  map_zero' := rfl
  map_add' _ _ := rfl

def constantPresheafToInteger :
    (Functor.const (Opens (TopCat.of B))ᵒᵖ).obj (AddCommGrpCat.of ℤ) ⟶
      (integerSheaf B).val where
  app U := AddCommGrpCat.ofHom (constantSection B U.unop)
  naturality _ _ _ := by
    apply AddCommGrpCat.ext
    intro n
    rfl

instance constantPresheafToInteger_locallyInjective :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (TopCat.of B))
      (constantPresheafToInteger B) where
  equalizerSieve_mem {U} m n h x hx := by
    refine ⟨U.unop, 𝟙 _, ?_, hx⟩
    change m = n
    exact congrArg (fun s : (integerSheaf B).val.obj U => s.hom ⟨x, hx⟩) h

instance constantPresheafToInteger_locallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (TopCat.of B))
      (constantPresheafToInteger B) where
  imageSieve_mem {U} s x hx := by
    let xU : U := ⟨x, hx⟩
    let T : Set U := s.hom ⁻¹' {s.hom xU}
    have hT : IsOpen T := (sectionLocallyConstant B U s).isLocallyConstant _
    let V : Opens B := ⟨Subtype.val '' T, U.isOpen.isOpenMap_subtype_val _ hT⟩
    have hVU : V ≤ U := by
      rintro y ⟨z, hz, rfl⟩
      exact z.2
    have hxV : x ∈ V := ⟨xU, rfl, rfl⟩
    refine ⟨V, homOfLE hVU, ⟨s.hom xU, ?_⟩, hxV⟩
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro y
    obtain ⟨z, hz, hzy⟩ := y.2
    have heq : (⟨y.1, hVU y.2⟩ : U) = z := Subtype.ext hzy.symm
    change s.hom xU = s.hom ⟨y.1, hVU y.2⟩
    rw [heq]
    exact hz.symm

instance constantPresheafToInteger_sheafify_isIso :
    IsIso ((presheafToSheaf (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat).map
      (constantPresheafToInteger B)) := by
  apply ((Opens.grothendieckTopology (TopCat.of B)).W_iff
    (constantPresheafToInteger B)).mp
  exact (Opens.grothendieckTopology (TopCat.of B)).W_of_isLocallyBijective
    (constantPresheafToInteger B)

/-- Canonical comparison, induced by the actual constant-section map. -/
def constantIntegerSheafIso :
    (constantSheaf (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ) ≅
    (integerSheaf B : Sheaf (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat) :=
  asIso ((presheafToSheaf (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat).map
    (constantPresheafToInteger B)) ≪≫
  asIso ((sheafificationAdjunction (Opens.grothendieckTopology (TopCat.of B))
    AddCommGrpCat).counit.app (integerSheaf B))

end
end QuaternionicSymmetry.LocallyConstantIntegerSheafComparison
