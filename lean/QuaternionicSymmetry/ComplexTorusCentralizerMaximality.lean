import QuaternionicSymmetry.ComplexTorusCompactCentralizer

/-! Maximality among actual connected commutative group images follows
from equality with the identity component of the compact centralizer.
This is a topological group statement; it does not infer holomorphicity
of a real-smooth parametrization in an auxiliary Lie atlas. -/

namespace QuaternionicSymmetry.ComplexTorusCentralizerMaximality

open TorusLaurentRepresentation IdentityComponentLie ComplexTorusCompactCentralizer

noncomputable section

variable {G K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup K] [TopologicalSpace K] [PreconnectedSpace K]
  {r : ℕ} (f : ComplexTorus r →* G)

/-- No strictly larger connected commutative group image can contain the
actual torus image once it is the identity component of its own compact
centralizer. In particular this applies to larger continuous torus actions. -/
theorem range_eq_of_contains
    (hRange : f.range = (Component (compactCentralizer f)).map
      (compactCentralizer f).subtype)
    (k : K →* G) (hk : Continuous k) (hContains : f.range ≤ k.range) :
    k.range = f.range := by
  apply le_antisymm ?_ hContains
  have hmem (t : K) : k t ∈ compactCentralizer f := by
    intro z hz
    obtain ⟨s, rfl⟩ := hz
    obtain ⟨u, hu⟩ := hContains ⟨compactInclusion r s, rfl⟩
    change f (compactInclusion r s) * k t = k t * f (compactInclusion r s)
    rw [← hu, ← map_mul, ← map_mul, mul_comm]
  let kC : K →* compactCentralizer f := k.codRestrict _ hmem
  have hkC : Continuous kC := hk.codRestrict _
  have hconn : IsConnected (Set.range kC) :=
    ⟨⟨kC 1, 1, rfl⟩, isPreconnected_range hkC⟩
  have hcomponent : kC.range ≤ Component (compactCentralizer f) :=
    hconn.subset_connectedComponent ⟨1, kC.map_one⟩
  rintro z ⟨t, rfl⟩
  rw [hRange]
  exact ⟨kC t, hcomponent ⟨t, rfl⟩, rfl⟩

end

end QuaternionicSymmetry.ComplexTorusCentralizerMaximality
