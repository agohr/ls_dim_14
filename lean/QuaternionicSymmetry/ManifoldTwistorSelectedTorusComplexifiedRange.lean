import QuaternionicSymmetry.ManifoldTwistorSelectedTorusComplexifiedDifferential
import QuaternionicSymmetry.RealComplexifiedMapRange

/-! The actual complexified selected compact-torus differential reaches its
defining complex-span Lie subalgebra H. This is not a group complexification
or a maximality statement. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedTorusComplexifiedRange

open ManifoldTwistorSelectedTorusComplexifiedDifferential
open RealToComplexTangentComplexification RealComplexifiedMapRange
open ManifoldTwistorSelectedContactTorusSmooth
open ManifoldTwistorSelectedContactToralLieSubalgebra
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicTorusAction
open ManifoldPositiveQuaternionicKahlerGeometry
open CompactLieTorusInputs
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open ComplexLieToralDifferentialSubalgebra
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {E M V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

theorem selectedTorusDifferentialIntoH_complexified_surjective
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hPreserve : FullPreservesContact P.tangent P.connection A C.contact.line)
    [hAutChart : ChartedSpace V
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hAutManifold : IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hAutLie : LieGroup 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    {r d : ℕ} (T : TorusEmbedding
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) r)
    (hTorusChart : ChartedSpace (Fin d → ℝ) (Torus r))
    (hTorusManifold : letI := hTorusChart
      IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
    (hTorusLie : letI := hTorusChart
      LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r)) :
    letI := A.charts
    letI := A.complexManifold
    letI := contactCharts (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactManifold (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactLieGroup (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := hTorusChart
    letI := hTorusManifold
    letI := hTorusLie
    Function.Surjective (complexifiedMapComplex
      (selectedTorusDifferentialIntoH (V := V)
        hR3 hClosed hImm hLee P n A C hPreserve T
        hTorusChart hTorusManifold hTorusLie)) := by
  letI := A.charts
  letI := A.complexManifold
  letI := contactCharts (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := hTorusChart
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := hTorusManifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := hTorusLie
  let ρ := selectedContactTorusHom P n A C T
  let hSmooth := selectedContactTorusHom_smooth (V := V)
    hR3 hClosed hImm hLee P n A C hPreserve T
    hTorusChart hTorusManifold hTorusLie
  let H := toralLieSubalgebra ρ hTorusChart hTorusManifold hTorusLie hSmooth
  let f := selectedTorusDifferentialIntoH (V := V)
    hR3 hClosed hImm hLee P n A C hPreserve T
    hTorusChart hTorusManifold hTorusLie
  apply surjective_complexifiedMapComplex_of_span_range_top f
  apply top_unique
  intro h _
  rcases h with ⟨x,hx⟩
  change (⟨x,hx⟩ : H) ∈ Submodule.span ℂ (Set.range f)
  induction hx using Submodule.span_induction with
  | mem s hs =>
      obtain ⟨w,rfl⟩ := hs
      exact Submodule.subset_span ⟨w,rfl⟩
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
      exact Submodule.add_mem _ (ihx (Submodule.mem_top)) (ihy (Submodule.mem_top))
  | smul a x hx ihx =>
      exact Submodule.smul_mem _ a (ihx (Submodule.mem_top))

end
end QuaternionicSymmetry.ManifoldTwistorSelectedTorusComplexifiedRange
