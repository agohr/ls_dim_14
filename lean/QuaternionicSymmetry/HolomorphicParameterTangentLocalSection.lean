import QuaternionicSymmetry.HolomorphicParameterTangent

/-! Joint holomorphicity of a partial derivative on a local holomorphic
tangent section. This is the variable-base counterpart of the existing
fixed-point `parameterTangent_contMDiff` theorem. -/
namespace QuaternionicSymmetry.HolomorphicParameterTangentLocalSection

open HolomorphicParameterTangent
open scoped Manifold ContDiff
noncomputable section

variable {P Z W V : Type*}
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace P] [ChartedSpace W P] [IsManifold 𝓘(ℂ,W) ∞ P]
  [TopologicalSpace Z] [ChartedSpace V Z] [IsManifold 𝓘(ℂ,V) ∞ Z]

theorem partialTangent_localSection_contMDiffOn
    (F : P × Z → Z)
    (hF : ContMDiff (𝓘(ℂ,W).prod 𝓘(ℂ,V)) 𝓘(ℂ,V) ∞ F)
    (U : Set Z)
    (σ : ∀ z : Z, TangentSpace 𝓘(ℂ,V) z)
    (hσ : ContMDiffOn 𝓘(ℂ,V) (𝓘(ℂ,V)).tangent ∞
      (fun z => (⟨z, σ z⟩ : TangentBundle 𝓘(ℂ,V) Z)) U) :
    ContMDiffOn (𝓘(ℂ,W).prod 𝓘(ℂ,V)) (𝓘(ℂ,V)).tangent ∞
      (fun q : P × Z => (⟨F q,
        mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) (fun y => F (q.1,y)) q.2 (σ q.2)⟩ :
          TangentBundle 𝓘(ℂ,V) Z)) (Set.univ ×ˢ U) := by
  let Ip := 𝓘(ℂ,W)
  let Iz := 𝓘(ℂ,V)
  have hzero : ContMDiffOn (Ip.prod Iz) Ip.tangent ∞
      (fun q : P × Z => (⟨q.1, 0⟩ : TangentBundle Ip P)) (Set.univ ×ˢ U) :=
    (Bundle.contMDiff_zeroSection ℂ _).comp_contMDiffOn contMDiffOn_fst
  have hsec : ContMDiffOn (Ip.prod Iz) Iz.tangent ∞
      (fun q : P × Z => (⟨q.2, σ q.2⟩ : TangentBundle Iz Z))
      (Set.univ ×ˢ U) :=
    hσ.comp contMDiffOn_snd (by intro q hq; exact hq.2)
  have hpair : ContMDiffOn (Ip.prod Iz) (Ip.tangent.prod Iz.tangent) ∞
      (fun q : P × Z =>
        ((⟨q.1,0⟩ : TangentBundle Ip P),
         (⟨q.2,σ q.2⟩ : TangentBundle Iz Z))) (Set.univ ×ˢ U) :=
    hzero.prodMk hsec
  have hlift : ContMDiffOn (Ip.prod Iz) (Ip.prod Iz).tangent ∞
      (fun q : P × Z => (⟨q,(0,σ q.2)⟩ :
        TangentBundle (Ip.prod Iz) (P × Z))) (Set.univ ×ˢ U) :=
    contMDiff_equivTangentBundleProd_symm.comp_contMDiffOn hpair
  have htotal := (hF.contMDiff_tangentMap (m := ∞) (by simp)).comp_contMDiffOn hlift
  apply htotal.congr
  intro q hq
  symm
  change (⟨F q, mfderiv (Ip.prod Iz) Iz F q (0,σ q.2)⟩ :
    TangentBundle Iz Z) = _
  congr 1
  exact (partial_mfderiv F hF q.1 q.2 (σ q.2)).symm

end
end QuaternionicSymmetry.HolomorphicParameterTangentLocalSection
