import QuaternionicSymmetry.DerivedExtensionClassFaithful

/-! The comparison detected by a derived extension class is an actual
isomorphism of middle objects, preserving both specified end maps. This
does not yet assert that every derived Ext¹ element is an extension. -/

namespace QuaternionicSymmetry.DerivedExtensionClassIso

open CategoryTheory CategoryTheory.Abelian
open DerivedExtensionClassFaithful
noncomputable section

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C]

theorem middle_map_isIso {X Y M N : C}
    (f : X ⟶ M) (g : M ⟶ Y) (hfg : f ≫ g = 0)
    (f' : X ⟶ N) (g' : N ⟶ Y) (hfg' : f' ≫ g' = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    (hT : (ShortComplex.mk f' g' hfg').ShortExact)
    (k : M ⟶ N) (hkf : f ≫ k = f') (hkg : k ≫ g' = g) : IsIso k := by
  let φ : ShortComplex.mk f g hfg ⟶ ShortComplex.mk f' g' hfg' := {
    τ₁ := 𝟙 X
    τ₂ := k
    τ₃ := 𝟙 Y
    comm₁₂ := by simpa only [Category.id_comp] using hkf.symm
    comm₂₃ := by simpa only [Category.comp_id] using hkg }
  letI : IsIso φ.τ₁ := by change IsIso (𝟙 X); infer_instance
  letI : IsIso φ.τ₃ := by change IsIso (𝟙 Y); infer_instance
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hS hT

variable [HasExt.{w} C]

theorem extClass_eq_iff_middle_iso {X Y M N : C}
    (f : X ⟶ M) (g : M ⟶ Y) (hfg : f ≫ g = 0)
    (f' : X ⟶ N) (g' : N ⟶ Y) (hfg' : f' ≫ g' = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    (hT : (ShortComplex.mk f' g' hfg').ShortExact) :
    hS.extClass = hT.extClass ↔
      ∃ e : M ≅ N, f ≫ e.hom = f' ∧ e.hom ≫ g' = g := by
  rw [extClass_eq_iff_middle_map f g hfg f' g' hfg' hS hT]
  constructor
  · rintro ⟨k, hkf, hkg⟩
    letI := middle_map_isIso f g hfg f' g' hfg' hS hT k hkf hkg
    exact ⟨asIso k, hkf, hkg⟩
  · rintro ⟨e, hef, heg⟩
    exact ⟨e.hom, hef, heg⟩

end
end QuaternionicSymmetry.DerivedExtensionClassIso
