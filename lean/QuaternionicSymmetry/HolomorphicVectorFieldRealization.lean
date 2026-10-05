import QuaternionicSymmetry.CompactHolomorphicVectorFieldFlow
import QuaternionicSymmetry.GeneralHolomorphicAutomorphismSecondCountable
import QuaternionicSymmetry.CompactLieOneParameterSmooth
import QuaternionicSymmetry.HolomorphicFamilyInfinitesimalLinear
import QuaternionicSymmetry.ComplexManifoldDerivativeScalarRestriction
import QuaternionicSymmetry.FaithfulActionInfinitesimal

/-! Every holomorphic vector field on a compact complex manifold is realized
by the orbit derivative in any supplied compatible complex Lie atlas on the
actual full automorphism group. Only the retained closed-subgroup theorem is
used to make the constructed continuous one-parameter subgroup smooth. -/
namespace QuaternionicSymmetry.HolomorphicVectorFieldRealization
open GeneralHolomorphicFullAutomorphisms GeneralClosedSubgroupLieSource
open CompactHolomorphicVectorFieldFlow HolomorphicFamilyInfinitesimalLinear
open ComplexLieRealCompanion ComplexManifoldDerivativeScalarRestriction
open ManifoldComplexHolomorphicFactorization
open scoped Manifold ContDiff
noncomputable section
variable {E V M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ,E) ∞ M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [CompactSpace M] [T2Space M] [Nonempty M] [SecondCountableTopology M]
  [ChartedSpace V (HolomorphicAutomorphisms E M)] [IsManifold 𝓘(ℂ,V) ∞ (HolomorphicAutomorphisms E M)]
  [LieGroup 𝓘(ℂ,V) ∞ (HolomorphicAutomorphisms E M)]
local notation "G" => HolomorphicAutomorphisms E M
local notation "S" => ContMDiffSection 𝓘(ℂ,E) E ∞ (TangentSpace 𝓘(ℂ,E) : M → Type _)

theorem hom_real_smooth (hClosed : LeeClosedEmbeddingTheorem) (X : S) :
    ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,V) ∞ (fun t : ℝ => hom X (Multiplicative.ofAdd t)) := by
  letI : IsManifold 𝓘(ℝ,V) ∞ G := realManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ G := realLieGroup
  letI : ChartedSpace ℝ (Multiplicative ℝ) := inferInstanceAs (ChartedSpace ℝ ℝ)
  letI : IsManifold 𝓘(ℝ,ℝ) ∞ (Multiplicative ℝ) := inferInstanceAs (IsManifold 𝓘(ℝ,ℝ) ∞ ℝ)
  letI : LieGroup 𝓘(ℝ,ℝ) ∞ (Multiplicative ℝ) := {
    contMDiff_mul := by
      change ContMDiff (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × ℝ => p.1+p.2)
      exact contMDiff_fst.add contMDiff_snd
    contMDiff_inv := by
      change ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun t : ℝ => -t)
      exact contMDiff_id.neg }
  exact ContinuousLieHomSmooth.continuous_hom_smooth (hom X) hClosed
    EquivariantImmersionFromMathlib.equivariantImmersion
    EmbeddedCodomainRestrictionFromMathlib.embeddedCodomainRestriction (hom_continuous X)

theorem infinitesimal_surjective (hClosed : LeeClosedEmbeddingTheorem)
    (hJoint : ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,E)) 𝓘(ℂ,E) ∞
      (fun p : G × M => p.1.1 p.2)) :
    Function.Surjective (infinitesimalActionLinear (fun p : G × M => p.1.1 p.2) 1 hJoint
      (by intro x; rfl)) := by
  letI : IsManifold 𝓘(ℝ,V) ∞ G := realManifold
  intro X
  let γ : ℝ → G := fun t => hom X (Multiplicative.ofAdd t)
  have hγ : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,V) ∞ γ := hom_real_smooth hClosed X
  have hγ₀ : γ 0 = 1 := (hom X).map_one
  let v : V := mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,V) γ 0 (1 : ℝ)
  refine ⟨v,?_⟩
  apply ContMDiffSection.ext
  intro x
  let a : G → M := fun g => g.1 x
  have hac : ContMDiff 𝓘(ℂ,V) 𝓘(ℂ,E) ∞ a := hJoint.comp (contMDiff_id.prodMk contMDiff_const)
  have har : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,E) ∞ a := holomorphic_is_real_smooth hac
  have he := mfderiv_real_eq_complex (har.mdifferentiableAt (by simp) (x := (1 : G)))
    (hac.mdifferentiableAt (by simp) (x := (1 : G)))
  change mfderiv 𝓘(ℂ,V) 𝓘(ℂ,E) a 1 v = X x
  change (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,E) a 1).restrictScalars ℝ v = X x
  rw [← he]
  have hcomp := mfderiv_comp (I := 𝓘(ℝ,ℝ)) (I' := 𝓘(ℝ,V)) (I'' := 𝓘(ℝ,E)) 0
    (har.mdifferentiableAt (by simp) (x := γ 0)) (hγ.mdifferentiableAt (by simp) (x := 0))
  rw [hγ₀] at hcomp
  have hh := congrArg (fun A : ℝ →L[ℝ] E => A 1) hcomp
  have hflow := congrArg (fun A : ℝ →L[ℝ] E => A 1) (integral X x 0).mfderiv
  change mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (flow X x) 0 (1 : ℝ) = (1 : ℝ) • X (flow X x 0) at hflow
  simp only [one_smul] at hflow
  have hx : (X : M → E) (flow X x 0) = X x := congrArg (X : M → E) (flow_zero X x)
  exact hh.symm.trans (hflow.trans hx)

theorem infinitesimal_injective
    (hJoint : ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,E)) 𝓘(ℂ,E) ∞
      (fun p : G × M => p.1.1 p.2)) :
    Function.Injective (infinitesimalActionLinear (fun p : G × M => p.1.1 p.2) 1 hJoint
      (by intro x; rfl)) := by
  letI : IsManifold 𝓘(ℝ,V) ∞ G := realManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ G := realLieGroup
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  have ha : ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
      (fun p : G × M => p.1.1 p.2) := by
    have hc := hJoint
    rw [← modelWithCornersSelf_prod] at hc ⊢
    letI : ChartedSpace (V × E) (G × M) := prodChartedSpace V G E M
    letI : IsManifold 𝓘(ℂ,V × E) ∞ (G × M) := by
      rw [modelWithCornersSelf_prod]
      exact IsManifold.prod G M
    letI : IsManifold 𝓘(ℝ,V × E) ∞ (G × M) := by
      rw [modelWithCornersSelf_prod]
      exact IsManifold.prod G M
    exact holomorphic_is_real_smooth (E := V × E) (F := E) hc
  apply FaithfulActionInfinitesimal.eq_zero_of_orbit_derivative_zero
    (fun p : G × M => p.1.1 p.2) ha (fun x => rfl) (fun g h x => rfl)
    (fun g hg => Subtype.ext (Diffeomorph.ext hg)) v
  intro x
  have hac : ContMDiff 𝓘(ℂ,V) 𝓘(ℂ,E) ∞ (fun g : G => g.1 x) :=
    hJoint.comp (contMDiff_id.prodMk contMDiff_const)
  have har : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,E) ∞ (fun g : G => g.1 x) :=
    ha.comp (contMDiff_id.prodMk contMDiff_const)
  rw [mfderiv_real_eq_complex (har.mdifferentiableAt (by simp) (x := (1 : G)))
    (hac.mdifferentiableAt (by simp) (x := (1 : G)))]
  exact congrArg (fun X : S => X x) hv

/-- The actual orbit derivative identifies the supplied automorphism Lie
algebra with all global holomorphic vector fields. -/
theorem infinitesimal_bijective (hClosed : LeeClosedEmbeddingTheorem)
    (hJoint : ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,E)) 𝓘(ℂ,E) ∞
      (fun p : G × M => p.1.1 p.2)) :
    Function.Bijective (infinitesimalActionLinear (fun p : G × M => p.1.1 p.2) 1 hJoint
      (by intro x; rfl)) :=
  ⟨infinitesimal_injective hJoint,infinitesimal_surjective hClosed hJoint⟩

end
end QuaternionicSymmetry.HolomorphicVectorFieldRealization
