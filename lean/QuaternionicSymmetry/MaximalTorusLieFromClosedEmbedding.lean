import QuaternionicSymmetry.CompactLieCommutingFlows
import QuaternionicSymmetry.CompactAbelianSubgroupTorus
import QuaternionicSymmetry.SelectedTorusLieSpanDerivativeEquality
import QuaternionicSymmetry.EquivariantImmersionFromMathlib
import QuaternionicSymmetry.EmbeddedCodomainRestrictionFromMathlib
import QuaternionicSymmetry.CommutingLieHomDerivatives
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! The original maximal-torus Lie correspondence follows from the retained
closed-subgroup theorem. Commuting tangent vectors integrate to commuting
flows; compact connected abelian closures are tori, so maximality puts the
flow back inside the same selected torus. -/
namespace QuaternionicSymmetry.MaximalTorusLieFromClosedEmbedding
open CompactLieTorusInputs CompactLieMaximalTorusTangentSource
open GeneralClosedSubgroupLieSource SelectedTorusEmbeddedLieAtlas
open SelectedTorusLieSpanDerivativeEquality CompactLieOneParameterSubgroup
open scoped Manifold ContDiff BigOperators
noncomputable section

private theorem circle_connected : ConnectedSpace Circle :=
  Function.Surjective.connectedSpace
    (fun z : Circle => ⟨Complex.arg z, Circle.exp_arg z⟩ : Function.Surjective Circle.exp)
    Circle.exp.continuous

local instance : ENat.LEInfty (minSmoothness ℝ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  {r : ℕ}

theorem torusLie_abelian (hClosed : LeeClosedEmbeddingTheorem)
    (T : TorusEmbedding G r) :
    ∀ x ∈ torusLieSpan (V := E) T, ∀ y ∈ torusLieSpan (V := E) T, ⁅x,y⁆ = 0 := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E) ∞
  obtain ⟨d,⟨B⟩⟩ := exists_selected_embedded_atlas (V := E) T hClosed
  letI := B.charts
  letI := B.manifold
  letI := B.lieGroup
  rw [torusLieSpan_eq_derivative_range T B
    EquivariantImmersionFromMathlib.equivariantImmersion
    EmbeddedCodomainRestrictionFromMathlib.embeddedCodomainRestriction]
  rintro _ ⟨v,rfl⟩ _ ⟨w,rfl⟩
  exact CommutingLieHomDerivatives.bracket_derivatives_eq_zero T.hom T.hom
    (selected_hom_smooth T B) (selected_hom_smooth T B)
    (fun a b => (Commute.all a b).map T.hom) v w

theorem torus_commutes_curve (hClosed : LeeClosedEmbeddingTheorem)
    (T : TorusEmbedding G r) (x : GroupLieAlgebra 𝓘(ℝ,E) G)
    (hx : ∀ y ∈ torusLieSpan (V := E) T, ⁅x,y⁆ = 0) :
    ∀ a t, Commute (T.hom a) (curve x t) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E) ∞
  letI : ConnectedSpace Circle := circle_connected
  obtain ⟨d,⟨B⟩⟩ := exists_selected_embedded_atlas (V := E) T hClosed
  letI := B.charts
  letI := B.manifold
  letI := B.lieGroup
  letI : SecondCountableTopology (Fin r → Circle) :=
    ChartedSpace.secondCountable_of_sigmaCompact (Fin d → ℝ) _
  letI : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,Fin d → ℝ) (Fin r → Circle)) :=
    inferInstanceAs (FiniteDimensional ℝ (Fin d → ℝ))
  let b := Module.finBasis ℝ (GroupLieAlgebra 𝓘(ℝ,Fin d → ℝ) (Fin r → Circle))
  intro a t
  obtain ⟨u,rfl⟩ := CompactAbelianLieCover.coordinateMap_surjective b hClosed a
  let S := (Subgroup.centralizer ({curve x t} : Set G)).comap T.hom
  have hgen (v : GroupLieAlgebra 𝓘(ℝ,Fin d → ℝ) (Fin r → Circle)) (s : ℝ) :
      curve v s ∈ S := by
    change T.hom (curve v s) ∈ Subgroup.centralizer ({curve x t} : Set G)
    rw [CompactLieOneParameterNaturality.map_curve T.hom (selected_hom_smooth T B)]
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (CompactLieCommutingFlows.curves_commute hClosed x
      (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,E) T.hom 1 v)
      (hx _ (derivative_range_le_torusLieSpan T B ⟨v,rfl⟩)) t s).eq.symm
  have hm : CompactAbelianLieCover.coordinateMap b u ∈ S := by
    apply S.prod_mem
    intro i _
    exact hgen (b i) (u i)
  exact Subgroup.mem_centralizer_singleton_iff.mp hm

theorem centralizing_curve_mem (hClosed : LeeClosedEmbeddingTheorem)
    (T : TorusEmbedding G r) (hMax : T.IsMaximal G)
    (x : GroupLieAlgebra 𝓘(ℝ,E) G)
    (hx : ∀ y ∈ torusLieSpan (V := E) T, ⁅x,y⁆ = 0) :
    ∀ t, curve x t ∈ T.hom.range := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E) ∞
  letI : ConnectedSpace Circle := circle_connected
  letI : ConnectedSpace (Multiplicative ℝ) := inferInstanceAs (ConnectedSpace ℝ)
  let hcomm := fun a s => torus_commutes_curve hClosed T x hx a (Multiplicative.toAdd s)
  let f : (Fin r → Circle) × Multiplicative ℝ →* G := T.hom.noncommCoprod (hom x) hcomm
  have hf : Continuous f :=
    (T.continuous_hom.comp continuous_fst).mul ((continuous_hom x).comp continuous_snd)
  let S := f.range
  have hS : IsConnected (S : Set G) := isConnected_range hf
  have hab : ∀ a b : S, a*b = b*a := fun a b => mul_comm a b
  have htorus := CompactAbelianSubgroupTorus.closure_isTorus (E := E) hClosed S hS hab
  have hT : T.hom.range ≤ S.topologicalClosure := by
    rintro g ⟨a,rfl⟩
    apply S.le_topologicalClosure
    exact ⟨(a,1),by simp [f]⟩
  have he := hMax S.topologicalClosure htorus hT
  intro t
  rw [← he]
  apply S.le_topologicalClosure
  exact ⟨(1,Multiplicative.ofAdd t),by simp [f,hom]⟩

theorem maximalTorusLieCorrespondence (hClosed : LeeClosedEmbeddingTheorem) :
    MaximalTorusLieCorrespondenceSource := by
  intro E G _ _ _ _ _ _ _ _ _ _ _ r T hMax
  refine ⟨torusLie_abelian hClosed T,?_⟩
  intro x hx
  apply Submodule.subset_span
  exact ⟨curve x, curve_zero x, centralizing_curve_mem hClosed T hMax x hx,
    CompactLieOneParameterSmooth.curve_smooth hClosed x, curve_derivative_zero x⟩

end
end QuaternionicSymmetry.MaximalTorusLieFromClosedEmbedding
