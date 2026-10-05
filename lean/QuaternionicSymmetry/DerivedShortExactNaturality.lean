import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! Naturality of the actual derived connecting morphism of a short exact
sequence. This is proved through the literal mapping-cone construction,
for use in comparing cocycle extensions. -/

namespace QuaternionicSymmetry.DerivedShortExactNaturality

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DerivedCategory CochainComplex
noncomputable section

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C]

theorem cone_map_desc {S T : ShortComplex (CochainComplex C ℤ)} (φ : S ⟶ T) :
    mappingCone.map S.f T.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm ≫ mappingCone.descShortComplex T =
      mappingCone.descShortComplex S ≫ φ.τ₃ := by
  ext n
  apply mappingCone.ext_from _ (n + 1) n rfl
  · simp [mappingCone.map, mappingCone.descShortComplex, Category.assoc]
  · simp only [HomologicalComplex.comp_f]
    simp only [mappingCone.map, mappingCone.inr_f_desc_f_assoc,
      HomologicalComplex.comp_f, Category.assoc,
      mappingCone.inr_f_descShortComplex_f, mappingCone.inr_f_descShortComplex_f_assoc]
    change (φ.τ₂ ≫ T.g).f n = (S.g ≫ φ.τ₃).f n
    rw [φ.comm₂₃]

variable [HasDerivedCategory.{w} C]

theorem triangleOfSESδ_naturality {S T : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) :
    Q.map φ.τ₃ ≫ triangleOfSESδ hT =
      triangleOfSESδ hS ≫ (Q.map φ.τ₁)⟦(1 : ℤ)⟧' := by
  letI := mappingCone.quasiIso_descShortComplex hS
  letI := mappingCone.quasiIso_descShortComplex hT
  let m := mappingCone.map S.f T.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm
  have hm : Q.map (mappingCone.descShortComplex S) ≫ Q.map φ.τ₃ =
      Q.map m ≫ Q.map (mappingCone.descShortComplex T) := by
    rw [← Q.map_comp, ← Q.map_comp]
    exact congrArg Q.map (cone_map_desc φ).symm
  have ht : Q.map m ≫ Q.map (mappingCone.triangle T.f).mor₃ =
      Q.map (mappingCone.triangle S.f).mor₃ ≫ Q.map (φ.τ₁⟦(1 : ℤ)⟧') := by
    rw [← Q.map_comp, ← Q.map_comp]
    exact congrArg Q.map
      (mappingCone.triangleMap S.f T.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm).comm₃.symm
  rw [← cancel_epi (Q.map (mappingCone.descShortComplex S))]
  dsimp only [triangleOfSESδ]
  simp only [← Category.assoc]
  rw [hm]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc (f := Q.map m), ht]
  simp only [Category.assoc]
  exact congrArg (fun t => Q.map (mappingCone.triangle S.f).mor₃ ≫ t)
    ((Q.commShiftIso (1 : ℤ)).hom.naturality φ.τ₁)

end
end QuaternionicSymmetry.DerivedShortExactNaturality
