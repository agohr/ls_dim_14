import QuaternionicSymmetry.ManifoldTwistorCoefficientSphere

/-! A fiber-bundle core for the actual quaternionic twistor sphere, now with
Mathlib's Euclidean two-sphere as its model fiber. This is a topological
bundle core; the differentiable sphere-bundle atlas is a subsequent step. -/

namespace QuaternionicSymmetry.ManifoldTwistorSphereCore

open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

/-- The Euclidean-sphere coordinate change, defined as identity outside its
overlap so the core can use it as a total function. -/
def euclideanSphereCoordChange (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞)) (i j : atlas E M) (x : M)
    (a : geometricSphere) : geometricSphere := by
  classical
  exact if h : x ∈ Q.frames.adaptedCore.baseSet i ∩ Q.frames.adaptedCore.baseSet j then
    coefficientSphereHomeomorph
      (sphereTransition Q i j x h.1 h.2
        (coefficientSphereHomeomorph.symm a))
  else a

theorem euclideanSphereCoordChange_self (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) (a : geometricSphere) :
    euclideanSphereCoordChange Q i i x a = a := by
  have hii : x ∈ Q.frames.adaptedCore.baseSet i ∩ Q.frames.adaptedCore.baseSet i :=
    ⟨hi, hi⟩
  change x ∈ (Q.frames.adaptedCore.localTriv i).baseSet ∩
    (Q.frames.adaptedCore.localTriv i).baseSet at hii
  dsimp [euclideanSphereCoordChange]
  rw [dif_pos hii, sphereTransition_self]
  simp

theorem euclideanSphereCoordChange_comp (i j k : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (hk : x ∈ Q.frames.adaptedCore.baseSet k) (a : geometricSphere) :
    euclideanSphereCoordChange Q j k x
        (euclideanSphereCoordChange Q i j x a) =
      euclideanSphereCoordChange Q i k x a := by
  have hij : x ∈ Q.frames.adaptedCore.baseSet i ∩ Q.frames.adaptedCore.baseSet j :=
    ⟨hi, hj⟩
  have hjk : x ∈ Q.frames.adaptedCore.baseSet j ∩ Q.frames.adaptedCore.baseSet k :=
    ⟨hj, hk⟩
  have hik : x ∈ Q.frames.adaptedCore.baseSet i ∩ Q.frames.adaptedCore.baseSet k :=
    ⟨hi, hk⟩
  change x ∈ (Q.frames.adaptedCore.localTriv i).baseSet ∩
    (Q.frames.adaptedCore.localTriv j).baseSet at hij
  change x ∈ (Q.frames.adaptedCore.localTriv j).baseSet ∩
    (Q.frames.adaptedCore.localTriv k).baseSet at hjk
  change x ∈ (Q.frames.adaptedCore.localTriv i).baseSet ∩
    (Q.frames.adaptedCore.localTriv k).baseSet at hik
  dsimp [euclideanSphereCoordChange]
  rw [dif_pos hij, dif_pos hjk, dif_pos hik]
  simp [sphereTransition_comp Q i j k x hi hj hk]

theorem continuousOn_euclideanSphereCoordChange (i j : atlas E M) :
    ContinuousOn (fun p : M × geometricSphere =>
      euclideanSphereCoordChange Q i j p.1 p.2)
      ((Q.frames.adaptedCore.baseSet i ∩
        Q.frames.adaptedCore.baseSet j) ×ˢ Set.univ) := by
  let h := coefficientSphereHomeomorph
  let Z := Q.quaternionicRankThreeCore
  let S : Set (M × geometricSphere) :=
    (Q.frames.adaptedCore.baseSet i ∩ Q.frames.adaptedCore.baseSet j) ×ˢ Set.univ
  change ContinuousOn (fun p : M × geometricSphere =>
    euclideanSphereCoordChange Q i j p.1 p.2) S
  rw [continuousOn_iff_continuous_restrict]
  have hf : Continuous (fun p : S => (p.1.1, (h.symm p.1.2).1)) :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_subtype_val.comp
        (h.symm.continuous.comp (continuous_snd.comp continuous_subtype_val)))
  have hmaps : ∀ p : S,
      (p.1.1, (h.symm p.1.2).1) ∈ (Z.baseSet i ∩ Z.baseSet j) ×ˢ Set.univ := by
    intro p
    exact ⟨p.2.1, Set.mem_univ _⟩
  have hc : Continuous (fun p : S =>
      Z.coordChange i j p.1.1 ((h.symm p.1.2).1)) :=
    by simpa only [Function.comp_def] using
      (Z.toFiberBundleCore.continuousOn_coordChange i j).comp_continuous hf hmaps
  have hs : Continuous (fun p : S =>
      (⟨Z.coordChange i j p.1.1 ((h.symm p.1.2).1),
        (squareNorm_transition Q i j p.1.1 p.2.1.1 p.2.1.2
          (h.symm p.1.2).1).trans (h.symm p.1.2).2⟩ : coefficientSphere)) :=
    hc.subtype_mk _
  have hh := h.continuous.comp hs
  exact hh.congr (by
    intro p
    have hp : p.1.1 ∈ (Q.frames.adaptedCore.localTriv i).baseSet ∩
        (Q.frames.adaptedCore.localTriv j).baseSet := p.2.1
    change h ⟨Z.coordChange i j p.1.1 ((h.symm p.1.2).1), _⟩ =
      euclideanSphereCoordChange Q i j p.1.1 p.1.2
    dsimp [euclideanSphereCoordChange]
    rw [dif_pos hp]
    apply congrArg h
    apply Subtype.ext
    rfl)

/-- The genuine associated two-sphere bundle core with Mathlib's geometric
sphere as its model fiber. Its transitions come from the actual quaternionic
tangent-frame reduction. -/
def sphereCore : FiberBundleCore (atlas E M) M geometricSphere where
  baseSet := Q.frames.adaptedCore.baseSet
  isOpen_baseSet := Q.frames.adaptedCore.isOpen_baseSet
  indexAt := Q.frames.adaptedCore.indexAt
  mem_baseSet_at := Q.frames.adaptedCore.mem_baseSet_at
  coordChange := euclideanSphereCoordChange Q
  coordChange_self := euclideanSphereCoordChange_self Q
  continuousOn_coordChange := continuousOn_euclideanSphereCoordChange Q
  coordChange_comp i j k x hx a :=
    euclideanSphereCoordChange_comp Q i j k x hx.1.1 hx.1.2 hx.2 a

def SphereBundleTotal := (sphereCore Q).TotalSpace

instance : TopologicalSpace (SphereBundleTotal Q) :=
  (sphereCore Q).toTopologicalSpace

instance : FiberBundle geometricSphere (sphereCore Q).Fiber :=
  (sphereCore Q).fiberBundle

/-- Bundle local trivializations first chart the total space over the
base–sphere product. -/
instance : ChartedSpace (M × geometricSphere) (SphereBundleTotal Q) :=
  FiberBundle.chartedSpace'

/-- The bundle is charted with model base times the genuine sphere. -/
instance : ChartedSpace (ModelProd E geometricSphere) (SphereBundleTotal Q) := by
  change ChartedSpace (ModelProd E geometricSphere)
    (Bundle.TotalSpace geometricSphere (sphereCore Q).Fiber)
  infer_instance

/-- Compose the fiber-bundle charts with Mathlib's stereographic charts to
obtain a charted total space with a Euclidean product model. -/
instance : ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin 2)))
    (SphereBundleTotal Q) := by
  letI : ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin 2)))
      (M × geometricSphere) := inferInstance
  exact ChartedSpace.comp _ (M × geometricSphere) _

/-- The associated geometric-sphere bundle and the earlier unit-subtype
construction have the same points over the same base. -/
def toOriginalSphere (p : SphereBundleTotal Q) : TwistorSphere Q :=
  pointOfLocal Q (Q.frames.adaptedCore.indexAt p.1) p.1
    (Q.frames.adaptedCore.mem_baseSet_at p.1)
    (coefficientSphereHomeomorph.symm p.2)

def fromOriginalSphere (z : TwistorSphere Q) : SphereBundleTotal Q :=
  ⟨projection Q z,
    coefficientSphereHomeomorph
      (localCoordinate Q (Q.frames.adaptedCore.indexAt (projection Q z)) z
        (Q.frames.adaptedCore.mem_baseSet_at (projection Q z)))⟩

def sphereTotalEquiv : SphereBundleTotal Q ≃ TwistorSphere Q where
  toFun := toOriginalSphere Q
  invFun := fromOriginalSphere Q
  left_inv p := by
    apply Bundle.TotalSpace.ext
    · rfl
    · apply heq_of_eq
      exact congrArg coefficientSphereHomeomorph
        (localCoordinate_pointOfLocal Q
          (Q.frames.adaptedCore.indexAt p.1) p.1
          (Q.frames.adaptedCore.mem_baseSet_at p.1)
          (coefficientSphereHomeomorph.symm p.2))
  right_inv z :=
    pointOfLocal_localCoordinate Q
      (Q.frames.adaptedCore.indexAt (projection Q z)) z
      (Q.frames.adaptedCore.mem_baseSet_at (projection Q z))

end
end QuaternionicSymmetry.ManifoldTwistorSphereCore
