import QuaternionicSymmetry.CompactActionLinearizingChart
import QuaternionicSymmetry.CompactActionInvariantNeighborhood

/-! Equivariant inverse charts identify the common fixed set with the fixed
linear subspace, on an actual invariant open neighborhood. -/
namespace QuaternionicSymmetry.CompactActionFixedLocalChart
open MeasureTheory Set CompactActionLinearizingChart CompactActionInvariantNeighborhood
open scoped Manifold ContDiff Topology
noncomputable section

variable {A E K : Type}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [ChartedSpace A K] [IsManifold 𝓘(ℝ,A) ∞ K] [LieGroup 𝓘(ℝ,A) ∞ K]
  [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
  (a : K × E → E) (ρ : K →* E →L[ℝ] E)

/-- The actual common fixed linear space of the tangent representation. -/
def fixedSubspace : Submodule ℝ E where
  carrier := {v | ∀ g, ρ g v = v}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw g; simp [map_add,hv g,hw g]
  smul_mem' := by intro c v hv g; simp [map_smul,hv g]

include μ in
lemma exists_fixed_local_chart
    {U : Set E} (hU : IsOpen U) (h0 : (0 : E) ∈ U)
    (ha : ContMDiffOn (𝓘(ℝ,A).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ a (univ ×ˢ U))
    (hρ : ContMDiff 𝓘(ℝ,A) 𝓘(ℝ,E →L[ℝ] E) ∞ ρ)
    (hz : ∀ g, a (g,0) = 0)
    (h1 : ∀ x, x ∈ U → a (1,x) = x)
    (hmul : ∀ g h x, x ∈ U → a (g,a (h,x)) = a (g*h,x))
    (hd : ∀ g, HasFDerivAt (fun x => a (g,x)) (ρ g) 0) :
    ∃ e : OpenPartialHomeomorph E E,
      0 ∈ e.source ∧ e.source ⊆ U ∧ e 0 = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ x ∈ e.source, ∀ g, a (g,x) ∈ e.source) ∧
      (∀ x ∈ e.source, ∀ g, e (a (g,x)) = ρ g (e x)) ∧
      (∀ x ∈ e.source, (∀ g, a (g,x) = x) ↔ e x ∈ fixedSubspace ρ) := by
  obtain ⟨e,he0,heU,heq,hezero,hesm,hesym⟩ :=
    exists_averaged_inverse_chart μ a ρ hU h0 ha hρ hz hd
  let V := U ∩ invariantCore a e.source
  have hV : IsOpen V := invariantCore_open hU ha.continuousOn e.open_source heU h1
  have hVsub : V ⊆ e.source := invariantCore_subset h1
  have hV0 : (0 : E) ∈ V := fixed_mem_invariantCore h0 he0 hz
  let c := e.restrOpen V hV
  have hcsource : c.source = V := by
    exact inter_eq_right.mpr hVsub
  have hcU : c.source ⊆ U := by rw [hcsource]; exact inter_subset_left
  have hcinv (x : E) (hx : x ∈ c.source) (g : K) : a (g,x) ∈ c.source := by
    rw [hcsource] at hx ⊢
    exact invariantCore_invariant heU hmul hx g
  have hceq (x : E) (hx : x ∈ c.source) (g : K) : c (a (g,x)) = ρ g (c x) := by
    change e (a (g,x)) = ρ g (e x)
    rw [heq]
    exact averaged_equivariant μ a ρ ha hρ hmul g (hcU hx)
  refine ⟨c,by rwa [hcsource],hcU,hezero,hesm.mono ?_,hesym.mono ?_,hcinv,hceq,?_⟩
  · exact inter_subset_left
  · exact inter_subset_left
  · intro x hx
    constructor
    · intro h g
      rw [← hceq x hx g,h g]
    · intro h g
      exact c.injOn (hcinv x hx g) hx ((hceq x hx g).trans (h g))

end
end QuaternionicSymmetry.CompactActionFixedLocalChart
