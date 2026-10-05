import QuaternionicSymmetry.VectorBundleFrameTransitions

/-! A source-free cocycle lemma for an endomorphism plane described in
each bundle chart by transporting one preferred-fiber plane. This is the
exact gluing mechanism needed for the concrete quotient Q-plane. -/

namespace QuaternionicSymmetry.ManifoldCorePlaneTransport

open VectorBundleFrameTransitions
open scoped Topology Bundle
noncomputable section

variable {ι B V : Type*} [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem localPlane_transport
    (Z : VectorBundleCore ℝ B V ι)
    (P : B → Submodule ℝ (V →L[ℝ] V))
    (L : ι → B → Submodule ℝ (V →L[ℝ] V))
    (hLocal : ∀ i x, x ∈ Z.baseSet i →
      L i x = Submodule.map
        ((transitionAtlas Z).adjointCoordChange (Z.indexAt x) i x).toLinearMap
        (P x))
    (i j : ι) (x : B) (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j) :
    Submodule.map ((transitionAtlas Z).adjointCoordChange i j x).toLinearMap
      (L i x) = L j x := by
  let T := transitionAtlas Z
  have hk : x ∈ Z.baseSet (Z.indexAt x) := Z.mem_baseSet_at x
  rw [hLocal i x hi, hLocal j x hj]
  ext a
  constructor
  · rintro ⟨b, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, (T.adjointCoordChange_comp (Z.indexAt x) i j x hk hi hj c).symm⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨T.adjointCoordChange (Z.indexAt x) i x c,
      ⟨c, hc, rfl⟩,
      T.adjointCoordChange_comp (Z.indexAt x) i j x hk hi hj c⟩

end
end QuaternionicSymmetry.ManifoldCorePlaneTransport
