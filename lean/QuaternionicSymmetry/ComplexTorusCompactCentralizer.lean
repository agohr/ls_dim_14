import QuaternionicSymmetry.ComplexTorusIdentityComponentLift
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Topology.Algebra.Group.Basic

/-! A complex-torus homomorphism factors through the actual closed
centralizer of its compact restriction. This is group topology, not a
claim that its parametrization is holomorphic in a target Lie atlas. -/

namespace QuaternionicSymmetry.ComplexTorusCompactCentralizer

open TorusLaurentRepresentation
noncomputable section

variable {r : ℕ} {G : Type*} [Group G] (f : ComplexTorus r →* G)

def compactCentralizer : Subgroup G :=
  Subgroup.centralizer (Set.range (f.comp (compactInclusion r)))

theorem mem_compactCentralizer (z : ComplexTorus r) :
    f z ∈ compactCentralizer f := by
  intro h hh
  obtain ⟨t, rfl⟩ := hh
  change f (compactInclusion r t) * f z =
    f z * f (compactInclusion r t)
  rw [← map_mul, ← map_mul]
  exact congrArg f (mul_comm (compactInclusion r t) z)

def intoCompactCentralizer : ComplexTorus r →* compactCentralizer f :=
  f.codRestrict (compactCentralizer f) (mem_compactCentralizer f)

@[simp] theorem intoCompactCentralizer_coe (z : ComplexTorus r) :
    (intoCompactCentralizer f z : G) = f z := rfl

theorem compactCentralizer_isClosed
    [TopologicalSpace G] [ContinuousMul G] [T2Space G] :
    IsClosed (compactCentralizer f : Set G) :=
  Set.isClosed_centralizer _

theorem intoCompactCentralizer_continuous
    [TopologicalSpace G] (hf : Continuous f) :
    Continuous (intoCompactCentralizer f) :=
  hf.codRestrict _

end
end QuaternionicSymmetry.ComplexTorusCompactCentralizer
