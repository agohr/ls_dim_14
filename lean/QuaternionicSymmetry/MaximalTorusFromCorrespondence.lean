import QuaternionicSymmetry.SelectedTorusEmbeddedLieAtlas
import QuaternionicSymmetry.InjectiveLieHomImmersion
import QuaternionicSymmetry.SmoothGroupHomSurjectiveDerivative
import QuaternionicSymmetry.CompactLieMaximalTorusTangentSource
import QuaternionicSymmetry.EquivariantImmersionFromMathlib
import QuaternionicSymmetry.EmbeddedCodomainRestrictionFromMathlib
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! The existence-only maximal-torus input is redundant. Embedded tori have
bounded dimension; one of largest dimension is inclusion maximal. The
retained maximal-abelian correspondence excludes the zero torus in positive
dimension. No exponential-map or compact-group classification is assumed. -/
namespace QuaternionicSymmetry.MaximalTorusFromCorrespondence
open CompactLieTorusInputs GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open SelectedTorusEmbeddedLieAtlas InjectiveLieHomImmersion ContinuousLieHomSmooth
open CompactLieMaximalTorusTangentSource
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 800000
local instance realMin : ENat.LEInfty (minSmoothness ℝ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

variable {V G : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Group G] [TopologicalSpace G] [T2Space G]
  [SecondCountableTopology G] [ChartedSpace V G]
  [IsManifold 𝓘(ℝ,V) ∞ G] [LieGroup 𝓘(ℝ,V) ∞ G]
  [IsTopologicalGroup G]

local notation "hImm" => EquivariantImmersionFromMathlib.equivariantImmersion
local notation "hRestrict" => EmbeddedCodomainRestrictionFromMathlib.embeddedCodomainRestriction

theorem atlas_dimension_bound {r d : ℕ} (T : TorusEmbedding G r)
    (g : EmbeddedRealLieAtlas V (Fin r → Circle) G T.hom d) :
    d ≤ Module.finrank ℝ V := by
  letI := g.charts
  letI := g.manifold
  letI := g.lieGroup
  have hi := smooth_injective_hom_immersion (E := Fin d → ℝ) (F := V) T.hom hImm
    (selected_hom_smooth T g) T.injective_hom 1
  let D : (Fin d → ℝ) →ₗ[ℝ] V :=
    (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) T.hom 1).toLinearMap
  have hd := LinearMap.finrank_le_finrank_of_injective (f := D) hi
  simpa using hd

def inclusionHom {r s : ℕ} (T : TorusEmbedding G r) (U : TorusEmbedding G s)
    (h : T.hom.range ≤ U.hom.range) : (Fin r → Circle) →* (Fin s → Circle) :=
  (MonoidHom.ofInjective U.injective_hom).symm.toMonoidHom.comp
    (T.hom.codRestrict U.hom.range (fun t => h ⟨t,rfl⟩))

theorem inclusionHom_spec {r s : ℕ} (T : TorusEmbedding G r) (U : TorusEmbedding G s)
    (h : T.hom.range ≤ U.hom.range) (t : Fin r → Circle) :
    U.hom (inclusionHom T U h t) = T.hom t :=
  MonoidHom.apply_ofInjective_symm U.injective_hom _

theorem range_eq_of_dimension_le (hClosed : LeeClosedEmbeddingTheorem)
    {r s d e : ℕ} (T : TorusEmbedding G r) (U : TorusEmbedding G s)
    (g : EmbeddedRealLieAtlas V (Fin r → Circle) G T.hom d)
    (k : EmbeddedRealLieAtlas V (Fin s → Circle) G U.hom e)
    (h : T.hom.range ≤ U.hom.range) (hed : e ≤ d) :
    T.hom.range = U.hom.range := by
  letI := g.charts
  letI := g.manifold
  letI := g.lieGroup
  letI := k.charts
  letI := k.manifold
  letI := k.lieGroup
  letI : ConnectedSpace Circle := by
    have hc : IsConnected (Set.range (fun t : ℝ => (Circle.exp t : ℂ))) :=
      isConnected_range (continuous_subtype_val.comp Circle.exp.continuous)
    have hr : Set.range (fun t : ℝ => (Circle.exp t : ℂ)) =
        (Submonoid.unitSphere ℂ : Set ℂ) := by
      ext z
      constructor
      · rintro ⟨t,rfl⟩
        exact (Circle.exp t).property
      · intro hz
        let q : Circle := ⟨z,hz⟩
        exact ⟨Complex.arg q, congrArg Subtype.val (Circle.exp_arg q)⟩
    exact isConnected_iff_connectedSpace.mp (hr ▸ hc)
  let f := inclusionHom T U h
  have hcomp : U.hom ∘ f = T.hom := funext (inclusionHom_spec T U h)
  have hc : Continuous f := U.isClosedEmbedding.isEmbedding.continuous_iff.mpr
    (by rw [hcomp]; exact T.continuous_hom)
  have hf := continuous_hom_smooth (E := Fin d → ℝ) (F := Fin e → ℝ) f hClosed hImm hRestrict hc
  have hi : Function.Injective f := by
    intro a b hab
    apply T.injective_hom
    rw [← inclusionHom_spec T U h a, ← inclusionHom_spec T U h b]
    exact congrArg U.hom hab
  have hdf := smooth_injective_hom_immersion (E := Fin d → ℝ) (F := Fin e → ℝ) f hImm hf hi 1
  let D : (Fin d → ℝ) →ₗ[ℝ] (Fin e → ℝ) :=
    (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,Fin e → ℝ) f 1).toLinearMap
  have hdim := LinearMap.finrank_le_finrank_of_injective (f := D) hdf
  have hde : d = e := by
    simp only [Module.finrank_pi, Fintype.card_fin] at hdim
    omega
  have hsurj : Function.Surjective
      (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,Fin e → ℝ) f 1) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := D)
      (by simpa using hde)).mp hdf
  have honto := SmoothGroupHomSurjectiveDerivative.surjective_of_surjective_mfderiv_one f hf hsurj
  apply le_antisymm h
  rintro z ⟨t,rfl⟩
  obtain ⟨u,hu⟩ := honto t
  exact ⟨u, by rw [← inclusionHom_spec T U h u]; exact congrArg U.hom hu⟩

include V in
/-- Maximizing the dimension suffices because proper inclusion of connected
embedded tori strictly increases dimension. -/
theorem exists_maximal_torus (hClosed : LeeClosedEmbeddingTheorem) :
    ∃ r : ℕ, ∃ T : TorusEmbedding G r, T.IsMaximal G := by
  let dims : Set ℕ := {d | ∃ r : ℕ, ∃ T : TorusEmbedding G r,
    Nonempty (EmbeddedRealLieAtlas V (Fin r → Circle) G T.hom d)}
  have hb : BddAbove dims := ⟨Module.finrank ℝ V, by
    rintro d ⟨r,T,⟨g⟩⟩
    exact atlas_dimension_bound T g⟩
  let T₀ : TorusEmbedding G 0 := {
    hom := 1
    continuous_hom := continuous_const
    injective_hom := fun _ _ _ => Subsingleton.elim _ _ }
  obtain ⟨d₀,hd₀⟩ := exists_selected_embedded_atlas (V := V) T₀ hClosed
  have hn : dims.Nonempty := ⟨d₀,0,T₀,hd₀⟩
  obtain ⟨d,⟨hd,hmax⟩⟩ := hb.exists_isGreatest_of_nonempty hn
  obtain ⟨r,T,⟨g⟩⟩ := hd
  refine ⟨r,T,?_⟩
  rintro S ⟨s,U,rfl⟩ hTU
  obtain ⟨e,⟨k⟩⟩ := exists_selected_embedded_atlas (V := V) U hClosed
  exact (range_eq_of_dimension_le hClosed T U g k hTU (hmax ⟨s,U,⟨k⟩⟩)).symm

/-- The zero torus has no nonzero velocity vectors. -/
theorem zero_torus_span (T : TorusEmbedding G 0) :
    torusLieSpan (V := V) T = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro v ⟨c,hc0,hr,hc,hv⟩
  have heq : c = fun _ => (1 : G) := by
    funext t
    obtain ⟨a,ha⟩ := hr t
    have ha1 : a = 1 := Subsingleton.elim _ _
    rw [ha1,map_one] at ha
    exact ha.symm
  rw [heq,mfderiv_const] at hv
  exact (Submodule.mem_bot ℝ).mpr (by simpa using hv.symm)

/-- The retained correspondence supplies the positive-rank clause of BG-L1. -/
theorem positive_maximal_torus
    [CompactSpace G] [ConnectedSpace G]
    (hClosed : LeeClosedEmbeddingTheorem)
    (hBG : MaximalTorusLieCorrespondenceSource)
    (hpos : 0 < Module.finrank ℝ V) :
    ∃ r : ℕ, 0 < r ∧ ∃ T : TorusEmbedding G r, T.IsMaximal G := by
  obtain ⟨r,T,hT⟩ := exists_maximal_torus (V := V) (G := G) hClosed
  refine ⟨r,?_,T,hT⟩
  by_contra h
  have hr : r = 0 := by omega
  subst r
  have hz := zero_torus_span (V := V) T
  have hs := (hBG V G T hT).2
  have hall : ∀ v : GroupLieAlgebra 𝓘(ℝ,V) G, v = 0 := by
    intro v
    have hv := hs v (by intro w hw; rw [hz,Submodule.mem_bot] at hw; rw [hw,lie_zero])
    rwa [hz,Submodule.mem_bot] at hv
  letI : Subsingleton V := ⟨fun v w => (hall v).trans (hall w).symm⟩
  have heq : Module.finrank ℝ V = 0 := Module.finrank_zero_of_subsingleton
  omega

/-- Exact original universally quantified existence contract, derived from
two other original contracts and the internal immersion proof. -/
theorem maximalTorusSource
    (hClosed : LeeClosedEmbeddingTheorem)
    (hBG : MaximalTorusLieCorrespondenceSource) : MaximalTorusSource.{0,0} := by
  intro V G hN hS hG hT hC hF hM hL hCompact hConnected hT2 hSecond hpos
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,V) ∞
  exact positive_maximal_torus hClosed hBG hpos

end
end QuaternionicSymmetry.MaximalTorusFromCorrespondence
