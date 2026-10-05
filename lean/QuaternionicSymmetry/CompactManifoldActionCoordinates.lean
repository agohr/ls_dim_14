import QuaternionicSymmetry.CompactActionDifferentialRepresentation

/-! A smooth compact action, transported to any smooth chart centered at a
fixed point, has the local linearizing chart constructed by averaging. -/
namespace QuaternionicSymmetry.CompactManifoldActionCoordinates
open Set CompactActionInvariantNeighborhood CompactActionDifferentialRepresentation
open CompactActionFixedLocalChart MeasureTheory
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 800000

variable {A E H K M : Type}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [ChartedSpace A K] [IsManifold 𝓘(ℝ,A) ∞ K] [LieGroup 𝓘(ℝ,A) ∞ K]
  [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]

include μ in
lemma exists_linearizing_chart
    (a : K × M → M) (ha : ContMDiff (𝓘(ℝ,A).prod I) I ∞ a)
    (h1 : ∀ x, a (1,x) = x)
    (hmul : ∀ g h x, a (g,a (h,x)) = a (g*h,x))
    (x : M) (hx : ∀ g, a (g,x) = x)
    (c : OpenPartialHomeomorph M E) (hxc : x ∈ c.source) (hc0 : c x = 0)
    (hc : ContMDiffOn I 𝓘(ℝ,E) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,E) I ∞ c.symm c.target) :
    ∃ (ρ : K →* E →L[ℝ] E) (e : OpenPartialHomeomorph M E),
      x ∈ e.source ∧ e.source ⊆ c.source ∧ e x = 0 ∧
      ContMDiffOn I 𝓘(ℝ,E) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ,E) I ∞ e.symm e.target ∧
      (∀ y ∈ e.source, ∀ g, a (g,y) ∈ e.source) ∧
      (∀ y ∈ e.source, ∀ g, e (a (g,y)) = ρ g (e y)) ∧
      (∀ y ∈ e.source, (∀ g, a (g,y) = y) ↔ e y ∈ fixedSubspace ρ) := by
  let V := (univ : Set M) ∩ invariantCore a c.source
  have hV : IsOpen V := invariantCore_open isOpen_univ
    (by simpa using ha.continuous)
    c.open_source (subset_univ _) (fun y _ => h1 y)
  have hVc : V ⊆ c.source := invariantCore_subset (fun y _ => h1 y)
  have hxV : x ∈ V := fixed_mem_invariantCore (mem_univ x) hxc hx
  have hVinv (y : M) (hy : y ∈ V) (g : K) : a (g,y) ∈ V :=
    invariantCore_invariant (subset_univ _) (fun g h y _ => hmul g h y) hy g
  let U := c.target ∩ c.symm ⁻¹' V
  have hU : IsOpen U := c.continuousOn_symm.isOpen_inter_preimage c.open_target hV
  have h00 : c.symm 0 = x := by rw [← hc0]; exact c.left_inv hxc
  have h0 : (0 : E) ∈ U := ⟨hc0 ▸ c.map_source hxc,by simpa only [mem_preimage,h00] using hxV⟩
  let b : K × E → E := fun p => c (a (p.1,c.symm p.2))
  have hb : ContMDiffOn (𝓘(ℝ,A).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ b (univ ×ˢ U) := by
    have hpair : ContMDiffOn (𝓘(ℝ,A).prod 𝓘(ℝ,E)) (𝓘(ℝ,A).prod I) ∞
        (fun p : K × E => (p.1,c.symm p.2)) (univ ×ˢ U) :=
      contMDiffOn_fst.prodMk (hci.comp contMDiffOn_snd (fun p hp => hp.2.1))
    exact hc.comp (ha.comp_contMDiffOn hpair) (fun p hp => hVc (hVinv _ hp.2.2 p.1))
  have hb0 (g : K) : b (g,0) = 0 := by simp only [b,h00,hx,hc0]
  have hb1 (y : E) (hy : y ∈ U) : b (1,y) = y := by
    simp only [b,h1,c.right_inv hy.1]
  have hbU (g : K) (y : E) (hy : y ∈ U) : b (g,y) ∈ U := by
    have hv := hVinv _ hy.2 g
    refine ⟨c.map_source (hVc hv),?_⟩
    change c.symm (c (a (g,c.symm y))) ∈ V
    rwa [c.left_inv (hVc hv)]
  have hbmul (g h : K) (y : E) (hy : y ∈ U) : b (g,b (h,y)) = b (g*h,y) := by
    change c (a (g,c.symm (c (a (h,c.symm y))))) = _
    rw [c.left_inv (hVc (hVinv _ hy.2 h)),hmul]
  let ρ := tangentRepresentation b (hU := hU) (h0 := h0) (ha := hb)
    (hz := hb0) (h1 := hb1) (hmul := hbmul)
  have hρ : ContMDiff 𝓘(ℝ,A) 𝓘(ℝ,E →L[ℝ] E) ∞ ρ :=
    tangentRepresentation_smooth b hU h0 hb hb0 hb1 hbmul
  obtain ⟨d,hd0,hdU,hdzero,hd,hdi,hdinv,hdeq,hdfix⟩ :=
    exists_fixed_local_chart μ b ρ hU h0 hb hρ hb0 hb1 hbmul
      (fun g => action_hasFDerivAt b hU h0 hb g)
  let e := c.trans d
  have hesub : e.source ⊆ c.source := inter_subset_left
  have hinv (y : M) (hy : y ∈ e.source) (g : K) : a (g,y) ∈ e.source := by
    have hcU := hdU hy.2
    have hyV : y ∈ V := by
      have hh : c.symm (c y) ∈ V := hcU.2
      rwa [c.left_inv hy.1] at hh
    have hbcy : b (g,c y) = c (a (g,y)) := by
      change c (a (g,c.symm (c y))) = _
      rw [c.left_inv hy.1]
    refine ⟨hVc (hVinv y hyV g),?_⟩
    change c (a (g,y)) ∈ d.source
    rw [← hbcy]
    exact hdinv (c y) hy.2 g
  have heq (y : M) (hy : y ∈ e.source) (g : K) : e (a (g,y)) = ρ g (e y) := by
    have hh := hdeq (c y) hy.2 g
    change d (c (a (g,c.symm (c y)))) = _ at hh
    rwa [c.left_inv hy.1] at hh
  refine ⟨ρ,e,⟨hxc,by change c x ∈ d.source; rwa [hc0]⟩,hesub,?_,?_,?_,hinv,heq,?_⟩
  · change d (c x) = 0
    rw [hc0,hdzero]
  · exact hd.contMDiffOn.comp (hc.mono inter_subset_left) (fun y hy => hy.2)
  · exact hci.comp (hdi.contMDiffOn.mono inter_subset_left) (fun y hy => hy.2)
  · intro y hy
    constructor
    · intro h g
      rw [← heq y hy g,h g]
    · intro h g
      exact e.injOn (hinv y hy g) hy ((heq y hy g).trans (h g))

end
end QuaternionicSymmetry.CompactManifoldActionCoordinates
