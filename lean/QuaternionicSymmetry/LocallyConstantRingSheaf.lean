import QuaternionicSymmetry.LocallyConstantIntegerSheafComparison

/-! Constant coefficients in any small discrete commutative ring are
canonically the actual sheaf of locally constant ring-valued functions.
This includes the finite coefficients needed for integral torsion. -/

namespace QuaternionicSymmetry.LocallyConstantRingSheaf

open CategoryTheory TopologicalSpace Opposite
noncomputable section

variable (B R : Type) [TopologicalSpace B] [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R] [DiscreteTopology R]

def sectionPresheaf : TopCat.Presheaf AddCommGrpCat (TopCat.of B) :=
  TopCat.presheafToTopCommRing (TopCat.of B) (TopCommRingCat.of R) ⋙
    forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

theorem sectionPresheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology (TopCat.of B))
      (sectionPresheaf B R) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat)]
  exact (TopCat.sheafToTop (X := TopCat.of B) (TopCat.of R)).cond

def sectionSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of B) :=
  ⟨sectionPresheaf B R, sectionPresheaf_isSheaf B R⟩

def sectionLocallyConstant (U : Opens B)
    (s : (sectionSheaf B R).val.obj (op U)) : LocallyConstant U R :=
  ⟨s.hom, (IsLocallyConstant.iff_continuous _).mpr s.hom.continuous⟩

def constantSection (U : Opens B) : R →+ (sectionSheaf B R).val.obj (op U) where
  toFun a := TopCat.ofHom (ContinuousMap.const U a)
  map_zero' := rfl
  map_add' _ _ := rfl

def constantPresheafToSections :
    (Functor.const (Opens (TopCat.of B))ᵒᵖ).obj (AddCommGrpCat.of R) ⟶
      (sectionSheaf B R).val where
  app U := AddCommGrpCat.ofHom (constantSection B R U.unop)
  naturality _ _ _ := by
    apply AddCommGrpCat.ext
    intro a
    rfl

instance constantPresheafToSections_locallyInjective :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (TopCat.of B))
      (constantPresheafToSections B R) where
  equalizerSieve_mem {U} a b h x hx := by
    refine ⟨U.unop, 𝟙 _, ?_, hx⟩
    change a = b
    exact congrArg (fun s : (sectionSheaf B R).val.obj U => s.hom ⟨x, hx⟩) h

instance constantPresheafToSections_locallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (TopCat.of B))
      (constantPresheafToSections B R) where
  imageSieve_mem {U} s x hx := by
    let xU : U := ⟨x, hx⟩
    let T : Set U := s.hom ⁻¹' {s.hom xU}
    have hT : IsOpen T := (sectionLocallyConstant B R U s).isLocallyConstant _
    let V : Opens B := ⟨Subtype.val '' T, U.isOpen.isOpenMap_subtype_val _ hT⟩
    have hVU : V ≤ U := by
      rintro y ⟨z, hz, rfl⟩
      exact z.2
    refine ⟨V, homOfLE hVU, ⟨s.hom xU, ?_⟩, ⟨xU, rfl, rfl⟩⟩
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro y
    obtain ⟨z, hz, hzy⟩ := y.2
    have heq : (⟨y.1, hVU y.2⟩ : U) = z := Subtype.ext hzy.symm
    change s.hom xU = s.hom ⟨y.1, hVU y.2⟩
    rw [heq]
    exact hz.symm

instance constantPresheafToSections_sheafify_isIso :
    IsIso ((presheafToSheaf (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat).map
      (constantPresheafToSections B R)) := by
  apply ((Opens.grothendieckTopology (TopCat.of B)).W_iff
    (constantPresheafToSections B R)).mp
  exact (Opens.grothendieckTopology (TopCat.of B)).W_of_isLocallyBijective
    (constantPresheafToSections B R)

def constantRingSheafIso :
    (constantSheaf (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat).obj
      (AddCommGrpCat.of R) ≅
    (sectionSheaf B R : Sheaf (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat) :=
  asIso ((presheafToSheaf (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat).map
    (constantPresheafToSections B R)) ≪≫
  asIso ((sheafificationAdjunction (Opens.grothendieckTopology (TopCat.of B))
    AddCommGrpCat).counit.app (sectionSheaf B R))

end
end QuaternionicSymmetry.LocallyConstantRingSheaf
