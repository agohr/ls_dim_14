import QuaternionicSymmetry.ManifoldQuaternionicReduction

/-! A smooth tangent frame gauge turns a transported plane of concrete
chart-coordinate endomorphisms into a genuine quaternionic reduction of its
adapted tangent core. The converse uses only frame inversion and cocycles. -/

namespace QuaternionicSymmetry.ManifoldTangentFramePlaneReduction

open Manifold
open ManifoldQuaternionicReduction
open VectorBundleFrameTransitions
open scoped Manifold Topology Bundle ContDiff
noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : WithTop ℕ∞} [IsManifold I (n + 1) M]

def chartConjugation (F : TangentFrameGauge I (M := M) (n := n))
    (i : atlas H M) (x : M) :
    (E →L[ℝ] E) →ₗ[ℝ] (E →L[ℝ] E) where
  toFun a := F.fromFrame i x * a * F.toFrame i x
  map_add' a b := by simp [mul_add, add_mul]
  map_smul' c a := by simp [mul_smul_comm, smul_mul_assoc]

theorem chartConjugation_injective
    (F : TangentFrameGauge I (M := M) (n := n))
    (i : atlas H M) (x : M)
    (hi : x ∈ F.adaptedCore.baseSet i) :
    Function.Injective (chartConjugation F i x) := by
  have hfi : F.toFrame i x * F.fromFrame i x = 1 := by
    ext v
    exact F.to_from i x hi v
  intro a b hab
  have hleft (c : E →L[ℝ] E) :
      F.toFrame i x * chartConjugation F i x c * F.fromFrame i x = c := by
    change F.toFrame i x * (F.fromFrame i x * c * F.toFrame i x) *
      F.fromFrame i x = c
    simp only [mul_assoc]
    rw [← mul_assoc (F.toFrame i x) (F.fromFrame i x), hfi]
    simp
  calc
    a = F.toFrame i x * chartConjugation F i x a * F.fromFrame i x :=
      (hleft a).symm
    _ = F.toFrame i x * chartConjugation F i x b * F.fromFrame i x := by rw [hab]
    _ = b := hleft b

theorem tangent_adjoint_chartConjugation
    (F : TangentFrameGauge I (M := M) (n := n))
    (i j : atlas H M) (x : M)
    (hj : x ∈ F.adaptedCore.baseSet j) (a : E →L[ℝ] E) :
    (transitionAtlas (tangentBundleCore I M)).adjointCoordChange i j x
      (chartConjugation F i x a) =
    chartConjugation F j x
      ((transitionAtlas F.adaptedCore).adjointCoordChange i j x a) := by
  rw [adjointCoordChange_apply, adjointCoordChange_apply]
  have hfj : F.fromFrame j x * F.toFrame j x = 1 := by
    ext v
    exact F.from_to j x hj v
  change (tangentBundleCore I M).coordChange i j x *
      (F.fromFrame i x * a * F.toFrame i x) *
      (tangentBundleCore I M).coordChange j i x =
    F.fromFrame j x *
      ((F.toFrame j x * (tangentBundleCore I M).coordChange i j x *
        F.fromFrame i x) * a *
        (F.toFrame i x * (tangentBundleCore I M).coordChange j i x *
          F.fromFrame j x)) * F.toFrame j x
  simp only [mul_assoc]
  rw [← mul_assoc (F.fromFrame j x) (F.toFrame j x), hfj]
  simp only [one_mul, mul_one]

def localPlane (F : TangentFrameGauge I (M := M) (n := n))
    (Q : QuaternionicStructure E) (i : atlas H M) (x : M) :
    Submodule ℝ (E →L[ℝ] E) :=
  Submodule.map (chartConjugation F i x) (quaternionicSpan Q)

def reduction_of_chartPlane_overlap
    (F : TangentFrameGauge I (M := M) (n := n))
    (Q : QuaternionicStructure E)
    (hOverlap : ∀ i j x, x ∈ F.adaptedCore.baseSet i →
      x ∈ F.adaptedCore.baseSet j →
      Submodule.map
        ((transitionAtlas (tangentBundleCore I M)).adjointCoordChange i j x).toLinearMap
        (localPlane F Q i x) = localPlane F Q j x) :
    QuaternionicFrameReduction F.adaptedCore where
  Q := fun _ => Q
  generator_transport := by
    intro i j x hi hj t
    let a := quaternionicGenerator Q t
    have ha : a ∈ quaternionicSpan Q := generator_mem_span Q t
    have hmap :
        (transitionAtlas (tangentBundleCore I M)).adjointCoordChange i j x
          (chartConjugation F i x a) ∈ localPlane F Q j x := by
      rw [← hOverlap i j x hi hj]
      exact ⟨chartConjugation F i x a, ⟨a, ha, rfl⟩, rfl⟩
    rw [tangent_adjoint_chartConjugation F i j x hj a] at hmap
    obtain ⟨b, hb, hbeq⟩ := hmap
    exact (chartConjugation_injective F j x hj hbeq).symm ▸ hb

end
end QuaternionicSymmetry.ManifoldTangentFramePlaneReduction
