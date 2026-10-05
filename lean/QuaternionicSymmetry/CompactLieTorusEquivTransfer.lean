import QuaternionicSymmetry.CompactLieTorusInputs

/-! Maximality among genuine torus subgroups is invariant under a
continuous group isomorphism with continuous inverse. -/

namespace QuaternionicSymmetry.CompactLieTorusEquivTransfer

open CompactLieTorusInputs
noncomputable section

variable {G H : Type*} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]

def transport {r : ℕ} (e : G ≃* H) (he : Continuous e)
    (T : TorusEmbedding G r) : TorusEmbedding H r where
  hom := e.toMonoidHom.comp T.hom
  continuous_hom := he.comp T.continuous_hom
  injective_hom := e.injective.comp T.injective_hom

theorem transport_maximal {r : ℕ}
    (e : G ≃* H) (he : Continuous e) (he' : Continuous e.symm)
    (T : TorusEmbedding G r) (hMax : T.IsMaximal G) :
    (transport e he T).IsMaximal H := by
  intro S hS hTS
  obtain ⟨s,U,hU⟩ := hS
  let Uback := transport e.symm he' U
  have hTU : T.hom.range ≤ Uback.hom.range := by
    intro g hg
    obtain ⟨t,rfl⟩ := hg
    have hmem : e (T.hom t) ∈ S := hTS ⟨t,rfl⟩
    rw [← hU] at hmem
    obtain ⟨u,hu⟩ := hmem
    refine ⟨u, ?_⟩
    change e.symm (U.hom u) = T.hom t
    rw [hu]
    exact e.symm_apply_apply _
  have hEq := hMax Uback.hom.range ⟨s,Uback,rfl⟩ hTU
  apply le_antisymm
  · intro h hh
    rw [← hU] at hh
    obtain ⟨u,hu⟩ := hh
    have hBack : Uback.hom u ∈ T.hom.range := hEq.symm ▸ ⟨u,rfl⟩
    obtain ⟨t,ht⟩ := hBack
    refine ⟨t, ?_⟩
    have hh' := congrArg e ht
    change e (T.hom t) = e (e.symm (U.hom u)) at hh'
    rw [e.apply_symm_apply] at hh'
    exact hh'.trans hu
  · exact hTS

end
end QuaternionicSymmetry.CompactLieTorusEquivTransfer
