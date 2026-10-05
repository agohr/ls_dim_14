import QuaternionicSymmetry.HolomorphicLineCorePullbackSections

/-! Every all-overlap holomorphic line gauge transports the entire global
section space. The preferred-chart scalar is used pointwise; regularity is
proved in fixed source and target charts using the overlap law.
-/

namespace QuaternionicSymmetry.HolomorphicLineGaugeSections

open HolomorphicLineGauge HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLinePowers
open scoped Manifold ContDiff Topology
noncomputable section
universe u

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (L W : LineCore.{u} (B := B) IB)

/-- Transport a section using the actual gauge in the preferred fibers.
All fixed-chart regularity follows from the gauge's four-chart law. -/
def mapSection
    (e : letI := L.holomorphic; letI := W.holomorphic
      GaugeIso (IB := IB) L.core W.core)
    (s : GlobalSections IB L) : GlobalSections IB W := by
  letI := L.holomorphic
  letI := W.holomorphic
  refine ⟨fun x => (e.forward (L.core.indexAt x) (W.core.indexAt x) x *
    (show ℂ from s x) : ℂ), ?_⟩
  intro x
  let i := L.core.indexAt x
  let a := W.core.indexAt x
  have hi : x ∈ L.core.baseSet i := L.core.mem_baseSet_at x
  have ha : x ∈ W.core.baseSet a := W.core.mem_baseSet_at x
  letI : MemTrivializationAtlas (L.core.localTriv i) := ⟨⟨i,rfl⟩⟩
  letI : MemTrivializationAtlas (W.core.localTriv a) := ⟨⟨a,rfl⟩⟩
  apply ((W.core.localTriv a).contMDiffAt_section_iff ha).2
  have hs : ContMDiffAt IB 𝓘(ℂ,ℂ) ∞
      (fun y => ((L.core.localTriv i) ⟨y,s y⟩).2) x :=
    ((L.core.localTriv i).contMDiffAt_section_iff hi).1 (s.contMDiff x)
  have he : ContMDiffAt IB 𝓘(ℂ,ℂ) ∞ (e.forward i a) x :=
    (e.forward_holomorphic i a x ⟨hi,ha⟩).contMDiffAt
      (((L.core.isOpen_baseSet i).inter (W.core.isOpen_baseSet a)).mem_nhds ⟨hi,ha⟩)
  apply (he.mul hs).congr_of_eventuallyEq
  filter_upwards [(L.core.isOpen_baseSet i).mem_nhds hi,
    (W.core.isOpen_baseSet a).mem_nhds ha] with y hyi hya
  change W.core.coordChange (W.core.indexAt y) a y
      (e.forward (L.core.indexAt y) (W.core.indexAt y) y * (show ℂ from s y)) =
    e.forward i a y * (L.core.coordChange (L.core.indexAt y) i y (s y))
  rw [linear_apply_one (W.core.coordChange (W.core.indexAt y) a y)
    (e.forward (L.core.indexAt y) (W.core.indexAt y) y * (show ℂ from s y)),
    linear_apply_one (L.core.coordChange (L.core.indexAt y) i y) (s y)]
  have hc := e.forward_compat (L.core.indexAt y) i (W.core.indexAt y) a y
    ⟨⟨⟨L.core.mem_baseSet_at y,hyi⟩,W.core.mem_baseSet_at y⟩,hya⟩
  change transitionScalar W.core (W.core.indexAt y) a y *
      (e.forward (L.core.indexAt y) (W.core.indexAt y) y * (show ℂ from s y)) =
    e.forward i a y * (transitionScalar L.core (L.core.indexAt y) i y *
      (show ℂ from s y))
  rw [← mul_assoc, hc, mul_assoc]

/-- A genuine complex-linear equivalence of all holomorphic sections,
with inverse supplied by the inverse gauge. -/
def sectionLinearEquiv
    (e : letI := L.holomorphic; letI := W.holomorphic
      GaugeIso (IB := IB) L.core W.core) :
    GlobalSections IB L ≃ₗ[ℂ] GlobalSections IB W := by
  letI := L.holomorphic
  letI := W.holomorphic
  exact {
    toFun := mapSection IB L W e
    invFun := mapSection IB W L e.symm
    left_inv := by
      intro s
      apply ContMDiffSection.ext
      intro x
      change e.backward (W.core.indexAt x) (L.core.indexAt x) x *
        (e.forward (L.core.indexAt x) (W.core.indexAt x) x *
          (show ℂ from s x)) = (show ℂ from s x)
      rw [← mul_assoc, e.left_inverse _ _ x
        ⟨L.core.mem_baseSet_at x,W.core.mem_baseSet_at x⟩, one_mul]
    right_inv := by
      intro s
      apply ContMDiffSection.ext
      intro x
      change e.forward (L.core.indexAt x) (W.core.indexAt x) x *
        (e.backward (W.core.indexAt x) (L.core.indexAt x) x *
          (show ℂ from s x)) = (show ℂ from s x)
      rw [← mul_assoc, e.right_inverse _ _ x
        ⟨W.core.mem_baseSet_at x,L.core.mem_baseSet_at x⟩, one_mul]
    map_add' := by
      intro s t
      apply ContMDiffSection.ext
      intro x
      change e.forward (L.core.indexAt x) (W.core.indexAt x) x *
        ((show ℂ from s x) + (show ℂ from t x)) =
        e.forward (L.core.indexAt x) (W.core.indexAt x) x * (show ℂ from s x) +
        e.forward (L.core.indexAt x) (W.core.indexAt x) x * (show ℂ from t x)
      exact mul_add _ _ _
    map_smul' := by
      intro c s
      apply ContMDiffSection.ext
      intro x
      change _ * (c * (show ℂ from s x)) = c * (_ * (show ℂ from s x))
      ring }

theorem sectionLinearEquiv_apply
    (e : letI := L.holomorphic; letI := W.holomorphic
      GaugeIso (IB := IB) L.core W.core)
    (s : GlobalSections IB L) (x : B) :
    letI := L.holomorphic
    letI := W.holomorphic
    sectionLinearEquiv IB L W e s x =
      e.forward (L.core.indexAt x) (W.core.indexAt x) x *
        (show ℂ from s x) := rfl

end
end QuaternionicSymmetry.HolomorphicLineGaugeSections
