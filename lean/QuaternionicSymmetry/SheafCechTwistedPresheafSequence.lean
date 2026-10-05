import QuaternionicSymmetry.SheafCechTwistedSectionKernel
import QuaternionicSymmetry.AbelianSheafCohomology
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! The cocycle defines an exact presheaf sequence with injective left
map and locally surjective right map to the constant integer presheaf.
Sheafification, not a false global surjectivity assertion, is needed next. -/

namespace QuaternionicSymmetry.SheafCechTwistedPresheafSequence

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open SheafCechOneCocycle SheafCechTwistedSections
open SheafCechTwistedSectionMaps SheafCechTwistedSectionKernel
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}
  {A : TopCat.Sheaf AddCommGrpCat (TopCat.of B)} {U : ι → Opens B}
  (c : OneCocycle A U)

def constantIntegerPresheaf : TopCat.Presheaf AddCommGrpCat (TopCat.of B) :=
  (Functor.const (Opens (TopCat.of B))ᵒᵖ).obj (AddCommGrpCat.of (ULift.{0} ℤ))

def inclusionNat : A.val ⟶ twistedPresheaf c where
  app V := AddCommGrpCat.ofHom (inclusion c V.unop)
  naturality V W f := by
    apply AddCommGrpCat.ext
    intro s
    exact (inclusion_restrict c f.unop.le s).symm

def projectionNat : twistedPresheaf c ⟶ constantIntegerPresheaf (B := B) where
  app V := AddCommGrpCat.ofHom {
    toFun := fun s => ULift.up (projection c V.unop s)
    map_zero' := rfl
    map_add' _ _ := rfl }
  naturality V W f := by
    apply AddCommGrpCat.ext
    intro s
    rfl

theorem inclusionNat_projectionNat : inclusionNat c ≫ projectionNat c = 0 := by
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro s
  rfl

def presheafComplex : ShortComplex ((Opens (TopCat.of B))ᵒᵖ ⥤ AddCommGrpCat) :=
  ShortComplex.mk (inclusionNat c) (projectionNat c) (inclusionNat_projectionNat c)

private theorem presheaf_exact_of_sectionwise
    {C : Type*} [Category C] (S : ShortComplex (C ⥤ AddCommGrpCat))
    (hS : ∀ V, (S.map ((evaluation C AddCommGrpCat).obj V)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext V
  exact (IsZero.of_iso
    ((ShortComplex.exact_iff_isZero_homology _).mp (hS V))
    (S.mapHomologyIso ((evaluation C AddCommGrpCat).obj V)).symm).eq_of_src _ _

variable (hcover : ∀ x : B, ∃ i, x ∈ U i)

include hcover in
theorem presheafComplex_exact : (presheafComplex c).Exact := by
  apply presheaf_exact_of_sectionwise
  intro V
  rw [ShortComplex.ab_exact_iff]
  intro s hs
  exact (kernel_iff c hcover V.unop s).mp (congrArg ULift.down hs)

include hcover in
theorem inclusionNat_mono : Mono (inclusionNat c) where
  right_cancellation {Z} f g h := by
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.ext
    intro s
    apply inclusion_injective c hcover V.unop
    exact congrArg (fun φ => φ.app V s) h

include hcover in
theorem projectionNat_locallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (TopCat.of B))
      (projectionNat c) where
  imageSieve_mem {V} n x hx := by
    obtain ⟨i, hi⟩ := hcover x
    refine ⟨V ⊓ U i, homOfLE inf_le_left,
      ⟨localLift c i (V ⊓ U i) inf_le_right n.down, ?_⟩, ⟨hx, hi⟩⟩
    rfl

end
end QuaternionicSymmetry.SheafCechTwistedPresheafSequence
