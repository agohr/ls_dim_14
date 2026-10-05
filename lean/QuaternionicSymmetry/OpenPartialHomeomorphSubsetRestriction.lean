import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! Restriction to corresponding subsets, with their induced topologies. -/
namespace QuaternionicSymmetry.OpenPartialHomeomorphSubsetRestriction
open Set
noncomputable section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (e : OpenPartialHomeomorph X Y) (S : Set X) (T : Set Y)
  [Nonempty S] [Nonempty T] (h : e.IsImage S T)

private def forward (x : S) : T := by
  classical
  exact if hx : x.1 ∈ e.source then ⟨e x.1,(h.apply_mem_iff hx).mpr x.2⟩
  else Classical.choice inferInstance

private def backward (y : T) : S := by
  classical
  exact if hy : y.1 ∈ e.target then ⟨e.symm y.1,(h.symm_apply_mem_iff hy).mpr y.2⟩
  else Classical.choice inferInstance

/-- Simultaneous restriction to corresponding subsets, even when the subsets
are not open in the ambient spaces. -/
def restrictSubsets : OpenPartialHomeomorph S T where
  toFun := forward e S T h
  invFun := backward e S T h
  source := Subtype.val ⁻¹' e.source
  target := Subtype.val ⁻¹' e.target
  map_source' := by
    intro x hx
    change (forward e S T h x).1 ∈ e.target
    simpa [forward,show x.1 ∈ e.source from hx] using e.map_source hx
  map_target' := by
    intro y hy
    change (backward e S T h y).1 ∈ e.source
    simpa [backward,show y.1 ∈ e.target from hy] using e.symm_mapsTo hy
  left_inv' := by
    intro x hx
    apply Subtype.ext
    simp [forward,backward,show x.1 ∈ e.source from hx,e.map_source hx,e.left_inv hx]
  right_inv' := by
    intro y hy
    apply Subtype.ext
    simp [backward,forward,show y.1 ∈ e.target from hy,e.symm_mapsTo hy,e.right_inv hy]
  open_source := e.open_source.preimage continuous_subtype_val
  open_target := e.open_target.preimage continuous_subtype_val
  continuousOn_toFun := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    apply (e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx => hx)).congr
    intro x hx
    simp [forward,show x.1 ∈ e.source from hx]
  continuousOn_invFun := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    apply (e.continuousOn_symm.comp continuous_subtype_val.continuousOn (fun _ hy => hy)).congr
    intro y hy
    simp [backward,show y.1 ∈ e.target from hy]

lemma restrictSubsets_apply {x : S} (hx : x.1 ∈ e.source) :
    (restrictSubsets e S T h x).1 = e x.1 := by
  change (forward e S T h x).1 = e x.1
  simp [forward,hx]

lemma restrictSubsets_symm_apply {y : T} (hy : y.1 ∈ e.target) :
    ((restrictSubsets e S T h).symm y).1 = e.symm y.1 := by
  change (backward e S T h y).1 = e.symm y.1
  simp [backward,hy]

end
end QuaternionicSymmetry.OpenPartialHomeomorphSubsetRestriction
