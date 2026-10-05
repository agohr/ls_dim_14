import QuaternionicSymmetry.IdentityComponentLie
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! Every compact torus in a topological group lies in its identity
component. Consequently a maximal torus of the identity component is
also maximal among torus subgroups of the full (possibly disconnected)
group. -/

namespace QuaternionicSymmetry.CompactLieTorusMaximalTransfer

open CompactLieTorusInputs IdentityComponentLie
noncomputable section

private theorem circle_connected : ConnectedSpace Circle := by
  have hconn : IsConnected
      (Set.range (fun t : ℝ => (Circle.exp t : ℂ))) :=
    isConnected_range (continuous_subtype_val.comp Circle.exp.continuous)
  have hrange : Set.range (fun t : ℝ => (Circle.exp t : ℂ)) =
      (Submonoid.unitSphere ℂ : Set ℂ) := by
    ext z
    constructor
    · rintro ⟨t,rfl⟩
      exact (Circle.exp t).property
    · intro hz
      let q : Circle := ⟨z,hz⟩
      exact ⟨Complex.arg q, congrArg Subtype.val (Circle.exp_arg q)⟩
  exact isConnected_iff_connectedSpace.mp (hrange ▸ hconn)

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem torus_range_le_component {r : ℕ} (T : TorusEmbedding G r) :
    T.hom.range ≤ Component G := by
  letI : ConnectedSpace Circle := circle_connected
  have hconn : IsConnected (Set.range T.hom) :=
    isConnected_range T.continuous_hom
  have hone : (1 : G) ∈ Set.range T.hom := by
    exact ⟨1, T.hom.map_one⟩
  exact hconn.subset_connectedComponent hone

def liftToComponent {r : ℕ} (T : TorusEmbedding G r) :
    TorusEmbedding (Component G) r where
  hom := {
    toFun t := ⟨T.hom t, torus_range_le_component G T ⟨t,rfl⟩⟩
    map_one' := by apply Subtype.ext; exact T.hom.map_one
    map_mul' t u := by apply Subtype.ext; exact T.hom.map_mul t u }
  continuous_hom := T.continuous_hom.subtype_mk _
  injective_hom := by
    intro t u h
    exact T.injective_hom (congrArg Subtype.val h)

theorem maximal_in_full_of_component {r : ℕ}
    (T : TorusEmbedding (Component G) r)
    (hMax : T.IsMaximal (Component G)) :
    let Tfull : TorusEmbedding G r := {
      hom := (Component G).subtype.comp T.hom
      continuous_hom := continuous_subtype_val.comp T.continuous_hom
      injective_hom := Subtype.val_injective.comp T.injective_hom }
    Tfull.IsMaximal G := by
  change ∀ S : Subgroup G, IsTorusSubgroup G S →
    ((Component G).subtype.comp T.hom).range ≤ S →
      S = ((Component G).subtype.comp T.hom).range
  intro S hS hTS
  obtain ⟨s,U,hU⟩ := hS
  let Uc := liftToComponent G U
  have hTU : T.hom.range ≤ Uc.hom.range := by
    intro g hg
    obtain ⟨t, rfl⟩ := hg
    have hmem : (T.hom t : G) ∈ S := hTS ⟨t,rfl⟩
    rw [← hU] at hmem
    obtain ⟨u,hu⟩ := hmem
    exact ⟨u, Subtype.ext hu⟩
  have hEq := hMax Uc.hom.range ⟨s,Uc,rfl⟩ hTU
  rw [← hU]
  ext g
  constructor
  · rintro ⟨u,hu⟩
    have huc : Uc.hom u ∈ T.hom.range := hEq.symm ▸ ⟨u,rfl⟩
    obtain ⟨t,ht⟩ := huc
    exact ⟨t, (congrArg Subtype.val ht).trans hu⟩
  · rintro ⟨t,ht⟩
    have htc : T.hom t ∈ Uc.hom.range := hEq ▸ ⟨t,rfl⟩
    obtain ⟨u,hu⟩ := htc
    exact ⟨u, (congrArg Subtype.val hu).trans ht⟩

end
end QuaternionicSymmetry.CompactLieTorusMaximalTransfer
