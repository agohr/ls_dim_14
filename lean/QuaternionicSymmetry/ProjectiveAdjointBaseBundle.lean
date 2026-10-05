import QuaternionicSymmetry.ProjectiveAdjointBundle
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.Sets.OpenCover

/-! A continuous adjoint bundle over an arbitrary topological base.

The transition functions below are supplied data. Their triple products may
differ by the same central sign in each direction; conjugation removes that
sign and gives an ordinary vector-bundle cocycle. This applies to manifold
bases, but neither a quaternionic frame atlas nor a connection is constructed
here. -/

namespace QuaternionicSymmetry.ProjectiveAdjointBaseBundle

open TopologicalSpace
open scoped Topology Bundle

noncomputable section

variable {ι B A : Type*} [TopologicalSpace B]
  [NormedRing A] [NormedAlgebra ℝ A]

local instance : NormedSpace ℝ A := NormedAlgebra.toNormedSpace A

/-- Projective gauge lifts on an open cover of any topological space. The
simultaneous sign in the triple law is explicit. -/
structure TransitionAtlas (ι B A : Type*) [TopologicalSpace B]
    [NormedRing A] [NormedAlgebra ℝ A] where
  U : ι → Opens B
  cover : TopologicalSpace.IsOpenCover U
  g : ι → ι → B → A
  diag : ∀ i x, x ∈ U i → g i i x = 1
  inverse : ∀ i j x, x ∈ U i → x ∈ U j → g i j x * g j i x = 1
  continuous : ∀ i j, ContinuousOn (g i j) ((U i : Set B) ∩ U j)
  cocycle : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k →
    ((g i j x * g j k x = g i k x) ∧
      (g k j x * g j i x = g k i x)) ∨
    ((g i j x * g j k x = -g i k x) ∧
      (g k j x * g j i x = -g k i x))

namespace TransitionAtlas

variable (P : TransitionAtlas ι B A)

/-- Conjugation is the coordinate change of the adjoint bundle. -/
def adjointCoordChange (i j : ι) (x : B) : A →L[ℝ] A :=
  ((ContinuousLinearMap.mul ℝ A) (P.g j i x)).comp
    (((ContinuousLinearMap.mul ℝ A).flip) (P.g i j x))

theorem adjointCoordChange_apply (i j : ι) (x : B) (a : A) :
    P.adjointCoordChange i j x a = P.g j i x * a * P.g i j x := by
  change P.g j i x * (a * P.g i j x) = _
  rw [mul_assoc]

theorem adjointCoordChange_self (i : ι) (x : B) (hx : x ∈ P.U i) (a : A) :
    P.adjointCoordChange i i x a = a := by
  rw [adjointCoordChange_apply, P.diag i x hx]
  simp

theorem adjointCoordChange_comp (i j k : ι) (x : B)
    (hi : x ∈ P.U i) (hj : x ∈ P.U j) (hk : x ∈ P.U k) (a : A) :
    P.adjointCoordChange j k x (P.adjointCoordChange i j x a) =
      P.adjointCoordChange i k x a := by
  simp only [adjointCoordChange_apply]
  have hmul : P.g k j x * (P.g j i x * a * P.g i j x) * P.g j k x =
      (P.g k j x * P.g j i x) * a * (P.g i j x * P.g j k x) := by
    simp only [mul_assoc]
  rw [hmul]
  rcases P.cocycle i j k x hi hj hk with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂]
  · rw [h₁, h₂]
    simp

theorem continuousOn_adjointCoordChange (i j : ι) :
    ContinuousOn (P.adjointCoordChange i j)
      ((P.U i : Set B) ∩ P.U j) := by
  have hji : ContinuousOn (P.g j i) ((P.U i : Set B) ∩ P.U j) := by
    simpa only [Set.inter_comm] using P.continuous j i
  exact (((ContinuousLinearMap.mul ℝ A).continuous.comp_continuousOn hji).clm_comp
    (((ContinuousLinearMap.mul ℝ A).flip).continuous.comp_continuousOn
      (P.continuous i j)))

/-- The projective gauge lifts produce a genuine continuous vector-bundle
core on the original base, without requiring a global lift of the projective
transitions. -/
def vectorCore : VectorBundleCore ℝ B A ι where
  baseSet i := P.U i
  isOpen_baseSet i := (P.U i).isOpen
  indexAt x := Classical.choose (P.cover.exists_mem x)
  mem_baseSet_at x := Classical.choose_spec (P.cover.exists_mem x)
  coordChange := P.adjointCoordChange
  coordChange_self i x hx a := P.adjointCoordChange_self i x hx a
  continuousOn_coordChange i j := P.continuousOn_adjointCoordChange i j
  coordChange_comp i j k x hx a :=
    P.adjointCoordChange_comp i j k x hx.1.1 hx.1.2 hx.2 a

/-- The associated mathlib topological vector-bundle structure. -/
def vectorBundleStructure : VectorBundle ℝ A P.vectorCore.Fiber :=
  P.vectorCore.vectorBundle

/-- The local trivialization is defined precisely over the corresponding
open set in the supplied atlas. -/
theorem mem_localTriv_source (i : ι) (x : B) (a : A) :
    (⟨x, a⟩ : P.vectorCore.TotalSpace) ∈ (P.vectorCore.localTriv i).source ↔
      x ∈ P.U i := by
  simpa only [vectorCore] using
    (P.vectorCore.mem_localTriv_source i (⟨x, a⟩ : P.vectorCore.TotalSpace))

/-- The bundle's actual coordinate change is conjugation by the supplied
projective gauge lifts. -/
theorem localTriv_coordChange (i j : ι) (x : B)
    (hi : x ∈ P.U i) (hj : x ∈ P.U j) (a : A) :
    (Trivialization.coordChangeL ℝ (P.vectorCore.localTriv i)
      (P.vectorCore.localTriv j) x) a =
      P.g j i x * a * P.g i j x := by
  have hb : x ∈ (P.vectorCore.localTriv i).baseSet ∧
      x ∈ (P.vectorCore.localTriv j).baseSet := by
    constructor
    · rw [← P.vectorCore.baseSet_at]
      exact hi
    · rw [← P.vectorCore.baseSet_at]
      exact hj
  calc
    _ = P.vectorCore.coordChange i j x a :=
      P.vectorCore.localTriv_coordChange_eq i j hb a
    _ = P.g j i x * a * P.g i j x := P.adjointCoordChange_apply i j x a

end TransitionAtlas
end
end QuaternionicSymmetry.ProjectiveAdjointBaseBundle

namespace QuaternionicSymmetry.ProjectiveAdjointDescent.GaugeAtlas

open QuaternionicSymmetry.ProjectiveAdjointBaseBundle

noncomputable section

variable {ι E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

/-- Every existing normed-space gauge atlas gives the new base-generic
transition atlas. This only forgets differentiability and connection data. -/
def toTransitionAtlas (P : GaugeAtlas ι E A) : TransitionAtlas ι E A where
  U := P.U
  cover := P.cover
  g := P.g
  diag := P.diag
  inverse := P.inverse
  continuous i j := by
    intro x hx
    exact (P.regular i j x hx.1 hx.2).continuousAt.continuousWithinAt
  cocycle i j k x hi hj hk := by
    rcases P.cocycle i j k x hi hj hk with ⟨hg, hh⟩ | ⟨hg, hh⟩
    · exact Or.inl ⟨hg.eq_of_nhds, hh.eq_of_nhds⟩
    · exact Or.inr ⟨hg.eq_of_nhds, hh.eq_of_nhds⟩

/-- The generic-base construction uses exactly the same adjoint coordinate
changes as the earlier normed-base construction. -/
theorem toTransitionAtlas_adjointCoordChange (P : GaugeAtlas ι E A)
    (i j : ι) (x : E) :
    P.toTransitionAtlas.adjointCoordChange i j x = P.adjointCoordChange i j x := rfl

theorem toTransitionAtlas_vectorCore_coordChange (P : GaugeAtlas ι E A)
    (i j : ι) (x : E) :
    P.toTransitionAtlas.vectorCore.coordChange i j x =
      P.vectorCore.coordChange i j x := rfl

end
end QuaternionicSymmetry.ProjectiveAdjointDescent.GaugeAtlas
