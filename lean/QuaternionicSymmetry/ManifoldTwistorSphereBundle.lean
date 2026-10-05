import QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal

/-!
The unit sphere of the actual metric quaternionic three-plane bundle. Its
fibers are the coefficient two-sphere, with transition maps inherited from
the adapted tangent frames. No complex or contact structure is asserted here.
-/

namespace QuaternionicSymmetry.ManifoldTwistorSphereBundle

open QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

instance : TopologicalSpace Q.quaternionicRankThreeCore.TotalSpace :=
  Q.quaternionicRankThreeCore.toTopologicalSpace

/-- The standard quadratic equation for the coefficient two-sphere. -/
def squareNorm (a : Fin 3 → ℝ) : ℝ := ∑ t : Fin 3, a t * a t

def coefficientSphere := {a : Fin 3 → ℝ // squareNorm a = 1}

instance : TopologicalSpace coefficientSphere := by
  unfold coefficientSphere
  infer_instance

theorem squareNorm_transition (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) (a : Fin 3 → ℝ) :
    squareNorm (Q.reduction.rankThreeCoordChange i j x a) = squareNorm a := by
  exact rankThreeCoordChange_dot Q i j x hi hj a a

/-- Preferred-coordinate unit vectors in the actual rank-three vector bundle. -/
def TwistorSphere :=
  {p : Q.quaternionicRankThreeCore.TotalSpace //
    squareNorm p.2 = 1}

instance : TopologicalSpace (TwistorSphere Q) := by
  unfold TwistorSphere
  infer_instance

/-- The projection of the actual sphere bundle to the quaternionic manifold. -/
def projection (z : TwistorSphere Q) : M := z.1.1

theorem projection_continuous : Continuous (projection Q) :=
  Q.quaternionicRankThreeCore.continuous_proj.comp continuous_subtype_val

/-- A unit vector expressed in any adapted quaternionic chart. -/
def localCoordinate (i : atlas E M) (z : TwistorSphere Q)
    (hi : projection Q z ∈ Q.frames.adaptedCore.baseSet i) :
    coefficientSphere := by
  let x := projection Q z
  let a := Q.quaternionicRankThreeCore.coordChange
    (Q.quaternionicRankThreeCore.indexAt x) i x z.1.2
  refine ⟨a, ?_⟩
  have hidx := Q.quaternionicRankThreeCore.mem_baseSet_at x
  exact (squareNorm_transition Q _ i x hidx hi z.1.2).trans z.2

/-- The point of the actual bundle represented by a local sphere coordinate. -/
def pointOfLocal (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (a : coefficientSphere) : TwistorSphere Q := by
  let b := Q.quaternionicRankThreeCore.coordChange i
    (Q.quaternionicRankThreeCore.indexAt x) x a.1
  refine ⟨⟨x, b⟩, ?_⟩
  have hidx := Q.quaternionicRankThreeCore.mem_baseSet_at x
  exact (squareNorm_transition Q i _ x hi hidx a.1).trans a.2

theorem projection_pointOfLocal (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) (a : coefficientSphere) :
    projection Q (pointOfLocal Q i x hi a) = x := rfl

theorem localCoordinate_pointOfLocal (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) (a : coefficientSphere) :
    localCoordinate Q i (pointOfLocal Q i x hi a)
      (by simpa [projection_pointOfLocal] using hi) = a := by
  apply Subtype.ext
  exact Q.quaternionicRankThreeCore.coordChange_comp i
    (Q.quaternionicRankThreeCore.indexAt x) i x
    ⟨⟨hi, Q.quaternionicRankThreeCore.mem_baseSet_at x⟩, hi⟩ a.1 |>.trans
    (Q.quaternionicRankThreeCore.coordChange_self i x hi a.1)

theorem pointOfLocal_localCoordinate (i : atlas E M) (z : TwistorSphere Q)
    (hi : projection Q z ∈ Q.frames.adaptedCore.baseSet i) :
    pointOfLocal Q i (projection Q z) hi (localCoordinate Q i z hi) = z := by
  apply Subtype.ext
  apply Bundle.TotalSpace.ext
  · rfl
  apply heq_of_eq
  change Q.quaternionicRankThreeCore.coordChange i
    (Q.quaternionicRankThreeCore.indexAt (projection Q z)) (projection Q z)
      (Q.quaternionicRankThreeCore.coordChange
        (Q.quaternionicRankThreeCore.indexAt (projection Q z)) i
        (projection Q z) z.1.2) = z.1.2
  rw [Q.quaternionicRankThreeCore.coordChange_comp
    (Q.quaternionicRankThreeCore.indexAt (projection Q z)) i
    (Q.quaternionicRankThreeCore.indexAt (projection Q z))
    (projection Q z)
    ⟨⟨Q.quaternionicRankThreeCore.mem_baseSet_at _, hi⟩,
      Q.quaternionicRankThreeCore.mem_baseSet_at _⟩,
    Q.quaternionicRankThreeCore.coordChange_self _ _
      (Q.quaternionicRankThreeCore.mem_baseSet_at _)]

/-- The part of the unit-sphere bundle above one adapted chart. -/
def localDomain (i : atlas E M) :=
  {z : TwistorSphere Q // projection Q z ∈ Q.frames.adaptedCore.baseSet i}

instance (i : atlas E M) : TopologicalSpace (localDomain Q i) := by
  unfold localDomain
  infer_instance

/-- A local product trivialization with the actual coefficient two-sphere.
Its transition is `sphereTransition`, whose norm and cocycle laws are below. -/
def localTrivialization (i : atlas E M) :
    localDomain Q i ≃
      {x : M // x ∈ Q.frames.adaptedCore.baseSet i} × coefficientSphere where
  toFun z := (⟨projection Q z.1, z.2⟩,
    localCoordinate Q i z.1 z.2)
  invFun xa := ⟨pointOfLocal Q i xa.1.1 xa.1.2 xa.2,
    by simp [projection_pointOfLocal]⟩
  left_inv z := by
    apply Subtype.ext
    exact pointOfLocal_localCoordinate Q i z.1 z.2
  right_inv xa := by
    apply Prod.ext
    · apply Subtype.ext
      exact projection_pointOfLocal Q i xa.1.1 xa.1.2 xa.2
    · exact localCoordinate_pointOfLocal Q i xa.1.1 xa.1.2 xa.2

/-- The local product equivalence is topological for the subtype topology
inherited from the actual rank-three vector bundle. -/
def localTrivializationHomeomorph (i : atlas E M) :
    localDomain Q i ≃ₜ
      {x : M // x ∈ Q.frames.adaptedCore.baseSet i} × coefficientSphere where
  toEquiv := localTrivialization Q i
  continuous_toFun := by
    let Z := Q.quaternionicRankThreeCore
    have hz : Continuous (fun z : localDomain Q i => (z.1.1 : Z.TotalSpace)) :=
      continuous_subtype_val.comp continuous_subtype_val
    have htriv : Continuous (fun z : localDomain Q i => (Z.localTriv i) z.1.1) :=
      (Z.localTriv i).continuousOn.comp_continuous hz (by
        intro z
        exact z.2)
    have hleft : Continuous (fun z : localDomain Q i =>
        (⟨projection Q z.1, z.2⟩ :
          {x : M // x ∈ Q.frames.adaptedCore.baseSet i})) :=
      (continuous_fst.comp htriv).subtype_mk _
    have hright : Continuous (fun z : localDomain Q i =>
        localCoordinate Q i z.1 z.2) :=
      (continuous_snd.comp htriv).subtype_mk _
    exact hleft.prodMk hright
  continuous_invFun := by
    let Z := Q.quaternionicRankThreeCore
    have hpair : Continuous (fun xa :
        {x : M // x ∈ Q.frames.adaptedCore.baseSet i} × coefficientSphere =>
          (xa.1.1, xa.2.1)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    have htotal : Continuous (fun xa :
        {x : M // x ∈ Q.frames.adaptedCore.baseSet i} × coefficientSphere =>
          (⟨xa.1.1, (Z.localTriv i).symm xa.1.1 xa.2.1⟩ : Z.TotalSpace)) :=
      (Z.localTriv i).continuousOn_symm.comp_continuous hpair (by
        intro xa
        exact ⟨xa.1.2, Set.mem_univ _⟩)
    have hsphere : Continuous (fun xa :
        {x : M // x ∈ Q.frames.adaptedCore.baseSet i} × coefficientSphere =>
          pointOfLocal Q i xa.1.1 xa.1.2 xa.2) :=
      (htotal.subtype_mk (by
        intro xa
        change squareNorm ((Z.localTriv i).symm xa.1.1 xa.2.1) = 1
        rw [Z.localTriv_symm_apply i xa.1.2 xa.2.1]
        exact (squareNorm_transition Q i _ xa.1.1 xa.1.2
          (Z.mem_baseSet_at _) xa.2.1).trans xa.2.2)).congr (by
        intro xa
        apply Subtype.ext
        apply Bundle.TotalSpace.ext
        · rfl
        · apply heq_of_eq
          exact Z.localTriv_symm_apply i xa.1.2 xa.2.1)
    exact hsphere.subtype_mk _

theorem localTrivialization_projection (i : atlas E M) (z : localDomain Q i) :
    (localTrivialization Q i z).1.1 = projection Q z.1 := rfl

theorem transition_sphere (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (a : coefficientSphere) :
    squareNorm (Q.reduction.rankThreeCoordChange i j x a.1) = 1 := by
  rw [squareNorm_transition Q i j x hi hj]
  exact a.2

/-- Transition of a two-sphere coordinate on an overlap. -/
def sphereTransition (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    coefficientSphere → coefficientSphere :=
  fun a => ⟨Q.reduction.rankThreeCoordChange i j x a.1,
    transition_sphere Q i j x hi hj a⟩

theorem sphereTransition_self (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) (a : coefficientSphere) :
    sphereTransition Q i i x hi hi a = a := by
  apply Subtype.ext
  exact Q.reduction.rankThreeCoordChange_self i x hi a.1

theorem sphereTransition_comp (i j k : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (hk : x ∈ Q.frames.adaptedCore.baseSet k) (a : coefficientSphere) :
    sphereTransition Q j k x hj hk (sphereTransition Q i j x hi hj a) =
      sphereTransition Q i k x hi hk a := by
  apply Subtype.ext
  exact Q.reduction.rankThreeCoordChange_comp i j k x hi hj hk a.1

/-- The ambient linear transition of the sphere charts is smooth as an
operator-valued map on each overlap. -/
theorem sphereTransition_ambient_smooth (i j : atlas E M) :
    ContMDiffOn 𝓘(ℝ, E)
      𝓘(ℝ, (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) ∞
      (Q.reduction.rankThreeCoordChange i j)
      (Q.frames.adaptedCore.baseSet i ∩ Q.frames.adaptedCore.baseSet j) :=
  Q.smooth_rankThreeCoordChange i j

theorem localTrivialization_transition (i j : atlas E M) (z : TwistorSphere Q)
    (hi : projection Q z ∈ Q.frames.adaptedCore.baseSet i)
    (hj : projection Q z ∈ Q.frames.adaptedCore.baseSet j) :
    localCoordinate Q j z hj =
      sphereTransition Q i j (projection Q z) hi hj (localCoordinate Q i z hi) := by
  apply Subtype.ext
  exact (Q.quaternionicRankThreeCore.coordChange_comp
    (Q.quaternionicRankThreeCore.indexAt (projection Q z)) i j
    (projection Q z)
    ⟨⟨Q.quaternionicRankThreeCore.mem_baseSet_at _, hi⟩, hj⟩ z.1.2).symm

end
end QuaternionicSymmetry.ManifoldTwistorSphereBundle
