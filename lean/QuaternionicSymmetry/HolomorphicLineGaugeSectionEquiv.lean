import QuaternionicSymmetry.HolomorphicLineLocalGaugeRatio
import QuaternionicSymmetry.HolomorphicLineCorePullbackSections

/-! A fiberwise line equivalence with holomorphic local witnesses transports
actual global holomorphic sections linearly. This is proved in bundle charts,
so no abstract sheaf-isomorphism premise is needed. -/
namespace QuaternionicSymmetry.HolomorphicLineGaugeSectionEquiv
open QuaternionicSymmetry.HolomorphicLineLocalGaugeRatio
open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.HolomorphicLineCorePullback
open QuaternionicSymmetry.HolomorphicLineGaugeFromBundleIso
open scoped Manifold ContDiff Topology
noncomputable section

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (L M : LineCore.{0} (B := B) IB)
  (e : ∀ x : B, L.core.Fiber x ≃ₗ[ℂ] M.core.Fiber x)

private theorem reconstruct (Z : VectorBundleCore ℂ B ℂ L.Index)
    (i : L.Index) (x : B) (v : Z.Fiber x)
    (hx : x ∈ Z.baseSet i) :
    v = ((Z.localTriv i) ⟨x,v⟩).2 • chartUnit Z i x := by
  let T := (Z.localTriv i).linearEquivAt (R := ℂ) x hx
  apply T.injective
  rw [T.map_smul]
  change T v = ((Z.localTriv i) ⟨x,v⟩).2 *
    ((Z.localTriv i) ⟨x,chartUnit Z i x⟩).2
  have h := Z.coordChange_comp i (Z.indexAt x) i x
    ⟨⟨hx,Z.mem_baseSet_at x⟩,hx⟩ (1 : ℂ)
  have hu : ((Z.localTriv i) ⟨x,chartUnit Z i x⟩).2 = 1 :=
    h.trans (Z.coordChange_self i x hx 1)
  rw [hu,mul_one]
  rfl

private theorem mapSection_contMDiffAt
    (h : HasLocalHolomorphicWitness IB L.core M.core e)
    (s : GlobalSections IB L) (x : B) :
    letI := L.holomorphic
    letI := M.holomorphic
    ContMDiffAt IB (IB.prod 𝓘(ℂ,ℂ)) ∞
      (fun y : B => (⟨y,e y (s y)⟩ : Bundle.TotalSpace ℂ M.core.Fiber)) x := by
  letI := L.holomorphic
  letI := M.holomorphic
  let i := L.core.indexAt x
  let a := M.core.indexAt x
  have hi : x ∈ L.core.baseSet i := L.core.mem_baseSet_at x
  have ha : x ∈ M.core.baseSet a := M.core.mem_baseSet_at x
  letI : MemTrivializationAtlas (L.core.localTriv i) := ⟨⟨i,rfl⟩⟩
  letI : MemTrivializationAtlas (M.core.localTriv a) := ⟨⟨a,rfl⟩⟩
  let d : B → ℂ := fun y => ((L.core.localTriv i) ⟨y,s y⟩).2
  let c := localScalar L.core M.core e i a
  have hd : ContMDiffAt IB 𝓘(ℂ,ℂ) ∞ d x :=
    ((L.core.localTriv i).contMDiffAt_section_iff hi).1 (s.contMDiff x)
  have hc : ContMDiffAt IB 𝓘(ℂ,ℂ) ∞ c x :=
    (localScalar_contMDiffOn_of_witness IB L.core M.core e h i a x
      ⟨hi,ha⟩).contMDiffAt
      ((L.core.isOpen_baseSet i).inter (M.core.isOpen_baseSet a) |>.mem_nhds ⟨hi,ha⟩)
  have hprod : ContMDiffAt IB 𝓘(ℂ,ℂ) ∞ (fun y => d y * c y) x :=
    hd.mul hc
  have hEq : (fun y => d y * c y) =ᶠ[𝓝 x]
      (fun y => ((M.core.localTriv a) ⟨y,e y (s y)⟩).2) := by
    filter_upwards [(L.core.isOpen_baseSet i).mem_nhds hi,
      (M.core.isOpen_baseSet a).mem_nhds ha] with y hy hya
    have hs := reconstruct IB L L.core i y (s y) hy
    rw [hs,map_smul]
    change ((L.core.localTriv i) ⟨y,s y⟩).2 *
      ((M.core.localTriv a) ⟨y,e y (chartUnit L.core i y)⟩).2 =
      ((M.core.localTriv a) ⟨y,
        ((L.core.localTriv i) ⟨y,s y⟩).2 • e y (chartUnit L.core i y)⟩).2
    exact (((M.core.localTriv a).linearEquivAt (R := ℂ) y
      hya).map_smul _ _).symm
  apply ((M.core.localTriv a).contMDiffAt_section_iff ha).2
  exact hprod.congr_of_eventuallyEq hEq.symm

/-- Actual pointwise fiber equivalences with local holomorphic witnesses
give a complex-linear equivalence of global holomorphic section spaces. -/
def sectionLinearEquivOfLocalWitness
    (h : HasLocalHolomorphicWitness IB L.core M.core e) :
    GlobalSections IB L ≃ₗ[ℂ] GlobalSections IB M := by
  letI := L.holomorphic
  letI := M.holomorphic
  let forward : GlobalSections IB L → GlobalSections IB M := fun s =>
    ⟨fun x => e x (s x), fun x => mapSection_contMDiffAt IB L M e h s x⟩
  let backward : GlobalSections IB M → GlobalSections IB L := fun s =>
    ⟨fun x => (e x).symm (s x), fun x =>
      mapSection_contMDiffAt IB M L (fun x => (e x).symm)
        (hasLocalHolomorphicWitness_symm IB L.core M.core e h) s x⟩
  exact {
    toFun := forward
    invFun := backward
    left_inv := by intro s; apply ContMDiffSection.ext; intro x; exact (e x).symm_apply_apply _
    right_inv := by intro s; apply ContMDiffSection.ext; intro x; exact (e x).apply_symm_apply _
    map_add' := by intro s t; apply ContMDiffSection.ext; intro x; exact map_add (e x) _ _
    map_smul' := by intro c s; apply ContMDiffSection.ext; intro x; exact map_smul (e x) c _ }

end
end QuaternionicSymmetry.HolomorphicLineGaugeSectionEquiv
