import QuaternionicSymmetry.ManifoldQuaternionicInducedLocalDerivativeSmooth

/-! The derivative of an immersion in any fixed pair of valid charts is
smooth throughout their overlap. No induced geometry is assumed. -/
namespace QuaternionicSymmetry.ManifoldImmersionFixedDerivativeSmooth
open ManifoldQuaternionicInducedLocalIntertwining
open ManifoldQuaternionicInducedLocalDerivativeSmooth
open scoped Manifold ContDiff Topology
noncomputable section
variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

theorem localDerivative_contMDiffAt (ι : N → M)
    (hι : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
    (i : atlas F N) (j : atlas E M) (x : N)
    (hi : x ∈ i.1.source) (hj : ι x ∈ j.1.source) :
    ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] E) ∞ (localDerivative ι i j) x := by
  let Z := tangentBundleCore 𝓘(ℝ,F) N
  let T := tangentBundleCore 𝓘(ℝ,E) M
  haveI : Z.IsContMDiff 𝓘(ℝ,F) ∞ := tangentBundleCore.isContMDiff
  haveI : T.IsContMDiff 𝓘(ℝ,E) ∞ := tangentBundleCore.isContMDiff
  have hleft : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (T.coordChange (achart E (ι x)) j) (ι x) :=
    (T.contMDiffOn_coordChange (n := ∞) 𝓘(ℝ,E) _ _).contMDiffAt
      (((T.isOpen_baseSet _).inter (T.isOpen_baseSet _)).mem_nhds
        ⟨mem_chart_source E (ι x),hj⟩)
  have hright : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] F) ∞
      (Z.coordChange i (achart F x)) x :=
    (Z.contMDiffOn_coordChange (n := ∞) 𝓘(ℝ,F) _ _).contMDiffAt
      (((Z.isOpen_baseSet _).inter (Z.isOpen_baseSet _)).mem_nhds
        ⟨hi,mem_chart_source F x⟩)
  have hs := (hleft.comp x hι.contMDiffAt).clm_comp
    ((localDerivative_smoothAt_center ι hι x).clm_comp hright)
  apply hs.congr_of_eventuallyEq
  filter_upwards [i.1.open_source.mem_nhds hi,
    (hι.continuous.continuousAt.preimage_mem_nhds (j.1.open_source.mem_nhds hj)),
    (chartAt F x).open_source.mem_nhds (mem_chart_source F x),
    (hι.continuous.continuousAt.preimage_mem_nhds
      ((chartAt E (ι x)).open_source.mem_nhds (mem_chart_source E (ι x))))]
    with y hyi hyj hyx hyιx
  ext v
  symm
  change T.coordChange (achart E (ι x)) j (ι y)
    (T.coordChange (achart E (ι y)) (achart E (ι x)) (ι y)
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι y
        (Z.coordChange (achart F x) (achart F y) y
          (Z.coordChange i (achart F x) y v)))) = _
  rw [Z.coordChange_comp i (achart F x) (achart F y) y
    ⟨⟨hyi,hyx⟩,mem_chart_source F y⟩]
  rw [T.coordChange_comp (achart E (ι y)) (achart E (ι x)) j (ι y)
    ⟨⟨mem_chart_source E (ι y),hyιx⟩,hyj⟩]
  rfl

end
end QuaternionicSymmetry.ManifoldImmersionFixedDerivativeSmooth
