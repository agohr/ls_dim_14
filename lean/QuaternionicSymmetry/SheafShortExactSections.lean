import QuaternionicSymmetry.AbelianSheafCohomology
import QuaternionicSymmetry.SheafCechRestrictionCalculus
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Sites.Limits

/-! Evaluation of a short exact sequence of actual abelian sheaves is
left exact. Its right map need not be surjective on sections. The unique
kernel preimages constructed here commute with restriction. -/

namespace QuaternionicSymmetry.SheafShortExactSections

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AbelianSheafCohomology SheafCechOneCocycle
noncomputable section

variable {B : Type} [TopologicalSpace B]

abbrev sections (V : Opens B) : AbelianSheaves B ⥤ AddCommGrpCat :=
  sheafToPresheaf (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat ⋙
    (evaluation (Opens (TopCat.of B))ᵒᵖ AddCommGrpCat).obj (op V)

theorem map_restrict {A M : AbelianSheaves B} (f : A ⟶ M)
    {V W : Opens B} (hWV : W ≤ V) (s : A.val.obj (op V)) :
    f.val.app (op W) (restrict A hWV s) =
      restrict M hWV (f.val.app (op V) s) := by
  exact congrArg (fun k => k s) (f.val.naturality (homOfLE hWV).op)

variable {S : ShortComplex (AbelianSheaves B)} (hS : S.ShortExact)

include hS in
theorem sections_exact (V : Opens B) : (S.map (sections V)).Exact :=
  hS.exact.map_of_mono_of_preservesKernel (sections V) hS.mono_f inferInstance

include hS in
theorem inclusion_injective (V : Opens B) :
    Function.Injective (S.f.val.app (op V)) := by
  letI := hS.mono_f
  exact (AddCommGrpCat.mono_iff_injective ((sections V).map S.f)).mp inferInstance

include hS in
theorem exists_kernelSection (V : Opens B) (s : S.X₂.val.obj (op V))
    (hs : S.g.val.app (op V) s = 0) :
    ∃ a : S.X₁.val.obj (op V), S.f.val.app (op V) a = s :=
  (ShortComplex.ab_exact_iff _).mp (sections_exact hS V) s hs

def kernelSection (V : Opens B) (s : S.X₂.val.obj (op V))
    (hs : S.g.val.app (op V) s = 0) : S.X₁.val.obj (op V) :=
  Classical.choose (exists_kernelSection hS V s hs)

@[simp] theorem inclusion_kernelSection (V : Opens B) (s : S.X₂.val.obj (op V))
    (hs : S.g.val.app (op V) s = 0) :
    S.f.val.app (op V) (kernelSection hS V s hs) = s :=
  Classical.choose_spec (exists_kernelSection hS V s hs)

theorem kernelSection_restrict {V W : Opens B} (hWV : W ≤ V)
    (s : S.X₂.val.obj (op V)) (hs : S.g.val.app (op V) s = 0)
    (hsW : S.g.val.app (op W) (restrict S.X₂ hWV s) = 0) :
    restrict S.X₁ hWV (kernelSection hS V s hs) =
      kernelSection hS W (restrict S.X₂ hWV s) hsW := by
  apply inclusion_injective hS W
  rw [map_restrict, inclusion_kernelSection, inclusion_kernelSection]

end
end QuaternionicSymmetry.SheafShortExactSections
