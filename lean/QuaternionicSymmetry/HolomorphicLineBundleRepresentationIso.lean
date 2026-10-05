import QuaternionicSymmetry.HolomorphicLineBundleCoreRepresentation

/-! Every actual holomorphic complex line bundle is holomorphically
fiberwise-linearly isomorphic to its represented core. Both total maps are
proved holomorphic in fixed local trivializations, not assumed smooth from
their pointwise definition. This closes bundle representability, but not
the equivalence with all invertible analytic sheaves or Picard cohomology. -/

namespace QuaternionicSymmetry.HolomorphicLineBundleRepresentationIso

open HolomorphicLineBundleCoreRepresentation HolomorphicLineCoreClasses Bundle
open scoped Manifold ContDiff Topology
noncomputable section

universe u v
variable {B : Type u} {H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (V : B → Type v) [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
  [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ∞ ℂ V IB]

theorem representationTotalMap_holomorphic :
    ContMDiff (IB.prod 𝓘(ℂ,ℂ)) (IB.prod 𝓘(ℂ,ℂ)) ∞
      (fun t : TotalSpace ℂ (bundleCore V).Fiber =>
        (⟨t.1, representationFiberEquiv V t.1 t.2⟩ : TotalSpace ℂ V)) := by
  intro t
  let i := t.1
  have hi : t.1 ∈ (trivializationAt ℂ V i).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt ℂ V t.1
  letI : MemTrivializationAtlas ((bundleCore V).localTriv i) := ⟨⟨i, rfl⟩⟩
  have hp : ContMDiffAt (IB.prod 𝓘(ℂ,ℂ)) IB ∞
      (fun p : TotalSpace ℂ (bundleCore V).Fiber => p.1) t :=
    Bundle.contMDiffAt_proj (bundleCore V).Fiber
  apply ((trivializationAt ℂ V i).contMDiffAt_iff
    ((trivializationAt ℂ V i).mem_source.2 hi)).2
  refine ⟨hp, ?_⟩
  have hs : ContMDiffAt (IB.prod 𝓘(ℂ,ℂ)) 𝓘(ℂ,ℂ) ∞
      (fun p : TotalSpace ℂ (bundleCore V).Fiber =>
        (((bundleCore V).localTriv i) p).2) t :=
    ((((bundleCore V).localTriv i).contMDiffAt_iff
      (((bundleCore V).mem_localTriv_source i t).2 hi)).1 contMDiffAt_id).2
  apply hs.congr_of_eventuallyEq
  have hi' := hp.continuousAt.preimage_mem_nhds
    ((trivializationAt ℂ V i).open_baseSet.mem_nhds hi)
  filter_upwards [hi'] with p hpi
  exact representationFiberEquiv_coordinates V i p.1 p.2 hpi

theorem representationInverse_coordinates
    (i x : B) (v : V x) (hx : x ∈ (trivializationAt ℂ V i).baseSet) :
    (((bundleCore V).localTriv i)
      ⟨x, (representationFiberEquiv V x).symm v⟩).2 =
      ((trivializationAt ℂ V i) ⟨x, v⟩).2 := by
  have h := representationFiberEquiv_coordinates V i x
    ((representationFiberEquiv V x).symm v) hx
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem representationInverseTotalMap_holomorphic :
    ContMDiff (IB.prod 𝓘(ℂ,ℂ)) (IB.prod 𝓘(ℂ,ℂ)) ∞
      (fun t : TotalSpace ℂ V =>
        (⟨t.1, (representationFiberEquiv V t.1).symm t.2⟩ :
          TotalSpace ℂ (bundleCore V).Fiber)) := by
  intro t
  let i := t.1
  have hi : t.1 ∈ (trivializationAt ℂ V i).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt ℂ V t.1
  letI : MemTrivializationAtlas ((bundleCore V).localTriv i) := ⟨⟨i, rfl⟩⟩
  have hp : ContMDiffAt (IB.prod 𝓘(ℂ,ℂ)) IB ∞
      (fun p : TotalSpace ℂ V => p.1) t :=
    Bundle.contMDiffAt_proj V
  apply (((bundleCore V).localTriv i).contMDiffAt_iff
    (f := fun p : TotalSpace ℂ V =>
      (⟨p.1, (representationFiberEquiv V p.1).symm p.2⟩ :
        TotalSpace ℂ (bundleCore V).Fiber)) (x₀ := t)
    (((bundleCore V).mem_localTriv_source i
      (⟨t.1, (representationFiberEquiv V t.1).symm t.2⟩ :
        TotalSpace ℂ (bundleCore V).Fiber)).2 hi)).2
  refine ⟨hp, ?_⟩
  have hs : ContMDiffAt (IB.prod 𝓘(ℂ,ℂ)) 𝓘(ℂ,ℂ) ∞
      (fun p : TotalSpace ℂ V => ((trivializationAt ℂ V i) p).2) t :=
    (((trivializationAt ℂ V i).contMDiffAt_iff
      ((trivializationAt ℂ V i).mem_source.2 hi)).1 contMDiffAt_id).2
  apply hs.congr_of_eventuallyEq
  have hi' := hp.continuousAt.preimage_mem_nhds
    ((trivializationAt ℂ V i).open_baseSet.mem_nhds hi)
  filter_upwards [hi'] with p hpi
  exact representationInverse_coordinates (V := V) i p.1 p.2 hpi

/-- A representation retains the actual fiber maps and both directions of
holomorphic regularity, not only an abstract equality of classes. -/
structure Representation where
  line : LineCore.{u} (B := B) IB
  fiberEquiv : ∀ x : B, line.core.Fiber x ≃ₗ[ℂ] V x
  holomorphicForward :
    letI := line.holomorphic
    ContMDiff (IB.prod 𝓘(ℂ,ℂ)) (IB.prod 𝓘(ℂ,ℂ)) ∞
      (fun t : TotalSpace ℂ line.core.Fiber =>
        (⟨t.1, fiberEquiv t.1 t.2⟩ : TotalSpace ℂ V))
  holomorphicBackward :
    letI := line.holomorphic
    ContMDiff (IB.prod 𝓘(ℂ,ℂ)) (IB.prod 𝓘(ℂ,ℂ)) ∞
      (fun t : TotalSpace ℂ V =>
        (⟨t.1, (fiberEquiv t.1).symm t.2⟩ : TotalSpace ℂ line.core.Fiber))

def bundleRepresentation : Representation IB V where
  line := representedLine IB V
  fiberEquiv := representationFiberEquiv V
  holomorphicForward := representationTotalMap_holomorphic IB V
  holomorphicBackward := representationInverseTotalMap_holomorphic IB V

theorem every_holomorphic_line_represented : Nonempty (Representation IB V) :=
  ⟨bundleRepresentation IB V⟩

end
end QuaternionicSymmetry.HolomorphicLineBundleRepresentationIso
