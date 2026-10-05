import QuaternionicSymmetry.HolomorphicLineOneFormCoordinates
import QuaternionicSymmetry.HolomorphicLinePowers

/-! Scalar local coordinates of holomorphic line sections, with their
literal transition law in manifold charts. -/
namespace QuaternionicSymmetry.HolomorphicLineSectionCoordinates
open HolomorphicLinePowers Filter
open scoped Manifold ContDiff Topology
noncomputable section
variable {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] [TopologicalSpace M] [ChartedSpace V M]
  [IsManifold 𝓘(ℂ,V) ∞ M]
  {ι : Type*} (L : VectorBundleCore ℂ M ℂ ι) [L.IsContMDiff 𝓘(ℂ,V) ∞]
  (s : ∀ x, L.Fiber x)

def localSection (a : ι) (x : M) : ℂ := L.coordChange (L.indexAt x) a x (s x)
def coordinateSection (i : atlas V M) (a : ι) (y : V) : ℂ := localSection L s a (i.1.symm y)

theorem coordinateSection_contDiffAt
    (hs : ContMDiff 𝓘(ℂ,V) ((𝓘(ℂ,V)).prod 𝓘(ℂ,ℂ)) ∞
      (fun x => (⟨x,s x⟩ : Bundle.TotalSpace ℂ L.Fiber)))
    (i : atlas V M) (a : ι) (x : M) (hi : x ∈ i.1.source) (ha : x ∈ L.baseSet a) :
    ContDiffAt ℂ ∞ (coordinateSection L s i a) (i.1 x) := by
  letI : MemTrivializationAtlas (L.localTriv a) := ⟨⟨a,rfl⟩⟩
  have hlocal : ContMDiffAt 𝓘(ℂ,V) 𝓘(ℂ,ℂ) ∞ (localSection L s a) x :=
    ((L.localTriv a).contMDiffAt_section_iff ha).1 (hs x)
  have hinv := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℂ,V)) (n := ∞)
    (IsManifold.subset_maximalAtlas i.2) (i.1.map_source hi)
  exact contMDiffAt_iff_contDiffAt.mp (hlocal.comp_of_eq hinv (i.1.left_inv hi))

theorem localSection_covariance (a b : ι) (x : M)
    (ha : x ∈ L.baseSet a) (hb : x ∈ L.baseSet b) :
    localSection L s b x = transitionScalar L a b x * localSection L s a x := by
  have h := L.coordChange_comp (L.indexAt x) a b x ⟨⟨L.mem_baseSet_at x,ha⟩,hb⟩ (s x)
  rw [linear_apply_one] at h
  exact h.symm

theorem coordinateSection_covariance_eventually (i j : atlas V M) (a b : ι) (x : M)
    (hi : x ∈ i.1.source) (hj : x ∈ j.1.source) (ha : x ∈ L.baseSet a) (hb : x ∈ L.baseSet b) :
    (fun y => coordinateSection L s j b (j.1 (i.1.symm y))) =ᶠ[𝓝 (i.1 x)]
      fun y => transitionScalar L a b (i.1.symm y) * coordinateSection L s i a y := by
  have hc := i.1.continuousAt_symm (i.1.map_source hi)
  have hj' : ∀ᶠ y in 𝓝 (i.1 x), i.1.symm y ∈ j.1.source :=
    hc.eventually (by simpa [i.1.left_inv hi] using j.1.open_source.mem_nhds hj)
  have ha' : ∀ᶠ y in 𝓝 (i.1 x), i.1.symm y ∈ L.baseSet a :=
    hc.eventually (by simpa [i.1.left_inv hi] using (L.isOpen_baseSet a).mem_nhds ha)
  have hb' : ∀ᶠ y in 𝓝 (i.1 x), i.1.symm y ∈ L.baseSet b :=
    hc.eventually (by simpa [i.1.left_inv hi] using (L.isOpen_baseSet b).mem_nhds hb)
  filter_upwards [hj',ha',hb'] with y hyj hya hyb
  simpa only [coordinateSection,j.1.left_inv hyj] using localSection_covariance L s a b (i.1.symm y) hya hyb

end
end QuaternionicSymmetry.HolomorphicLineSectionCoordinates
