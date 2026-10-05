import QuaternionicSymmetry.CompactLieTorusMaximalTransfer

/-! Maximality of a torus of a possibly disconnected group restricts back
to its actual identity component. -/

namespace QuaternionicSymmetry.IdentityComponentMaximalTorusReverse

open CompactLieTorusInputs CompactLieTorusMaximalTransfer IdentityComponentLie
noncomputable section

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem maximal_in_component_of_full {r : ℕ} (T : TorusEmbedding G r)
    (hMax : T.IsMaximal G) :
    (liftToComponent G T).IsMaximal (Component G) := by
  intro S hS hTS
  obtain ⟨s,U,hU⟩ := hS
  let Ufull : TorusEmbedding G s := {
    hom := (Component G).subtype.comp U.hom
    continuous_hom := continuous_subtype_val.comp U.continuous_hom
    injective_hom := Subtype.val_injective.comp U.injective_hom }
  have hTU : T.hom.range ≤ Ufull.hom.range := by
    intro g hg
    obtain ⟨t,rfl⟩ := hg
    have hmem : (liftToComponent G T).hom t ∈ S := hTS ⟨t,rfl⟩
    rw [← hU] at hmem
    obtain ⟨u,hu⟩ := hmem
    exact ⟨u, congrArg Subtype.val hu⟩
  have hEq := hMax Ufull.hom.range ⟨s,Ufull,rfl⟩ hTU
  rw [← hU]
  ext g
  constructor
  · rintro ⟨u,hu⟩
    have hgu : (Ufull.hom u : G) ∈ T.hom.range := hEq.symm ▸ ⟨u,rfl⟩
    obtain ⟨t,ht⟩ := hgu
    exact ⟨t, Subtype.ext (ht.trans (congrArg Subtype.val hu))⟩
  · rintro ⟨t,ht⟩
    have hgt : (T.hom t : G) ∈ Ufull.hom.range := hEq ▸ ⟨t,rfl⟩
    obtain ⟨u,hu⟩ := hgt
    exact ⟨u, Subtype.ext (hu.trans (congrArg Subtype.val ht))⟩

end
end QuaternionicSymmetry.IdentityComponentMaximalTorusReverse
