import QuaternionicSymmetry.SheafCechTwistedPresheafSequence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! An actual Čech one-cocycle gives a genuine short exact sequence of
abelian sheaves, and hence a class in Mathlib's derived H¹. The extension
is constructed from twisted sections and exact sheafification. Invariance
under cocycle comparison and the classification converse remain separate. -/

namespace QuaternionicSymmetry.SheafCechExtension

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open SheafCechOneCocycle SheafCechTwistedPresheafSequence AbelianSheafCohomology
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}
  {A : TopCat.Sheaf AddCommGrpCat (TopCat.of B)} {U : ι → Opens B}
  (c : OneCocycle A U) (hcover : ∀ x : B, ∃ i, x ∈ U i)

abbrev sheafification :=
  presheafToSheaf (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat

def sheafifiedComplex : ShortComplex (AbelianSheaves B) :=
  (presheafComplex c).map (sheafification (B := B))

include hcover in
theorem sheafifiedComplex_shortExact : (sheafifiedComplex c).ShortExact where
  exact := (presheafComplex_exact c hcover).map _
  mono_f := by
    letI := inclusionNat_mono c hcover
    change Mono ((sheafification (B := B)).map (inclusionNat c))
    infer_instance
  epi_g := by
    letI := projectionNat_locallySurjective c hcover
    letI : Sheaf.IsLocallySurjective
        ((sheafification (B := B)).map (projectionNat c)) :=
      (Presheaf.isLocallySurjective_presheafToSheaf_map_iff
        (Opens.grothendieckTopology (TopCat.of B)) (projectionNat c)).mpr inferInstance
    change Epi ((sheafification (B := B)).map (projectionNat c))
    infer_instance

def originalSheafIso : (sheafification (B := B)).obj A.val ≅ A :=
  asIso ((sheafificationAdjunction
    (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat).counit.app A)

/-- The extension has the original actual sheaf, not an unrelated
isomorphic coefficient object, as its kernel. -/
def extensionComplex : ShortComplex (AbelianSheaves B) :=
  ShortComplex.mk ((originalSheafIso (A := A)).inv ≫ (sheafifiedComplex c).f)
    (sheafifiedComplex c).g (by
      rw [Category.assoc, (sheafifiedComplex c).zero, comp_zero])

def extensionComplexIso : extensionComplex c ≅ sheafifiedComplex c :=
  ShortComplex.isoMk (originalSheafIso (A := A)).symm (Iso.refl _) (Iso.refl _)
    (by simp [extensionComplex]) (by simp [extensionComplex])

include hcover in
theorem extensionComplex_shortExact : (extensionComplex c).ShortExact :=
  ShortComplex.shortExact_of_iso (extensionComplexIso c).symm
    (sheafifiedComplex_shortExact c hcover)

/-- The genuine derived-cohomology class of a cocycle on a cover. No
new definition of H¹ is introduced. -/
def cohomologyClass : cohomology B A 1 :=
  (extensionComplex_shortExact c hcover).extClass

end
end QuaternionicSymmetry.SheafCechExtension
