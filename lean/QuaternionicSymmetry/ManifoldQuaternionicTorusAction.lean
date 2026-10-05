import QuaternionicSymmetry.ManifoldQuaternionicSpanSymmetry
import Mathlib.Analysis.Complex.Circle

/-!
Continuous compact-torus actions on genuine quaternionic Hermitian manifolds.
Each torus element is represented by a smooth metric/quaternionic isometry;
joint continuity is recorded explicitly. This is the symmetry object needed
before fixed components, weight characters, or Lie-rank arguments can be
instantiated on an actual manifold.
-/

namespace QuaternionicSymmetry.ManifoldQuaternionicTorusAction

open ManifoldQuaternionicSpanSymmetry
open scoped Manifold ContDiff
noncomputable section

/-- The standard compact real torus of rank `r`. -/
abbrev Torus (r : ℕ) := Fin r → Circle

/-- An integral weight defines the usual multiplicative torus character.
No primitivity condition is imposed. -/
def weightCharacter {r : ℕ} (μ : Fin r → ℤ) : Torus r →* Circle where
  toFun t := ∏ i : Fin r, t i ^ μ i
  map_one' := by simp
  map_mul' s t := by
    simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

/-- The full weight kernel can be disconnected when the weight is not
primitive; the fixed-component argument uses its identity component. -/
def weightKernel {r : ℕ} (μ : Fin r → ℤ) : Subgroup (Torus r) :=
  (weightCharacter μ).ker

/-- The identity component of the weight kernel, viewed again as a subgroup
of the ambient torus. This is the `S=(ker μ)⁰` in the symmetry proof. -/
def connectedWeightKernel {r : ℕ} (μ : Fin r → ℤ) : Subgroup (Torus r) :=
  (Subgroup.connectedComponentOfOne (weightKernel μ)).map (weightKernel μ).subtype

theorem connectedWeightKernel_le_kernel {r : ℕ} (μ : Fin r → ℤ) :
    connectedWeightKernel μ ≤ weightKernel μ := by
  intro t ht
  obtain ⟨s, _, rfl⟩ := ht
  exact s.2

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- A continuous torus action by smooth quaternionic isometries. Faithfulness
is stated separately, since fixed-subtorus arguments deliberately use actions
with nontrivial kernel. -/
structure ContinuousTorusAction (r : ℕ) where
  representation : Torus r →* QuaternionicIsometries Q
  continuous_action : Continuous
    (fun p : Torus r × M => representation p.1 • p.2)

namespace ContinuousTorusAction

variable {r : ℕ} (A : ContinuousTorusAction Q r)

def imageSubgroup : Subgroup (QuaternionicIsometries Q) :=
  A.representation.range

/-- The connected kernel of an integral character, acting through the
actual quaternionic-isometry representation. -/
def connectedKernelImage (μ : Fin r → ℤ) :
    Subgroup (QuaternionicIsometries Q) :=
  (connectedWeightKernel μ).map A.representation

/-- The ambient-manifold fixed locus for the connected weight kernel. -/
def connectedKernelFixedSet (μ : Fin r → ℤ) : Set M :=
  fixedPoints Q (connectedKernelImage Q A μ)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem isClosed_connectedKernelFixedSet [T2Space M]
    (μ : Fin r → ℤ) : IsClosed (connectedKernelFixedSet Q A μ) :=
  isClosed_fixedPoints Q (connectedKernelImage Q A μ)

/-- The connected fixed component through `x` for the connected weight
kernel. It is empty when `x` is not fixed. -/
def connectedKernelFixedComponent (μ : Fin r → ℤ) (x : M) : Set M :=
  connectedComponentIn (connectedKernelFixedSet Q A μ) x

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem fixedComponent_subset_fixedSet (μ : Fin r → ℤ) (x : M) :
    connectedKernelFixedComponent Q A μ x ⊆
      connectedKernelFixedSet Q A μ :=
  connectedComponentIn_subset _ _

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem fixedComponent_connected (μ : Fin r → ℤ) (x : M) :
    IsPreconnected (connectedKernelFixedComponent Q A μ x) :=
  isPreconnected_connectedComponentIn

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem self_mem_fixedComponent (μ : Fin r → ℤ) (x : M)
    (hx : x ∈ connectedKernelFixedSet Q A μ) :
    x ∈ connectedKernelFixedComponent Q A μ x :=
  mem_connectedComponentIn hx

/-- Points fixed by every element of this concrete torus action. -/
def fixedSet : Set M := fixedPoints Q A.imageSubgroup

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem mem_fixedSet_iff (x : M) :
    x ∈ A.fixedSet ↔ ∀ t : Torus r, A.representation t • x = x := by
  simp [fixedSet, fixedPoints, imageSubgroup]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem isClosed_fixedSet [T2Space M] : IsClosed A.fixedSet :=
  isClosed_fixedPoints Q A.imageSubgroup

/-- An injective torus representation witnesses a genuine torus subgroup of
the quaternionic isometry group. -/
def Faithful : Prop := Function.Injective A.representation

end ContinuousTorusAction

/-- A concrete lower bound for quaternionic isometry torus rank. This asks
for a faithful continuous action by the standard rank-`r` torus. -/
def HasTorusRankAtLeast (r : ℕ) : Prop :=
  ∃ A : ContinuousTorusAction Q r, A.Faithful

end
end QuaternionicSymmetry.ManifoldQuaternionicTorusAction
