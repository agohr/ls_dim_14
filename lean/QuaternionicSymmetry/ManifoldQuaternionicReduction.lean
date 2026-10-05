import QuaternionicSymmetry.VectorBundleFrameTransitions
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
Adapted frames of the actual tangent bundle. A smooth gauge changes the
standard chart-derivative frames to frames in which local quaternionic
endomorphism triples are constant. The triples may rotate on overlaps.
-/

namespace QuaternionicSymmetry.ManifoldQuaternionicReduction

open Bundle TopologicalSpace
open scoped Manifold Topology Bundle ContDiff

/-- The tangent-frame API asks for one extra derivative; smooth regularity
is unchanged by adding one. This spelling needs an explicit instance. -/
instance smoothOrderAddOne {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] :
    IsManifold I (∞ + 1) M := by
  simpa using (inferInstance : IsManifold I ∞ M)

noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : WithTop ℕ∞} [IsManifold I (n + 1) M]

/-- Smooth choices of local tangent frames, expressed relative to the actual
chart derivative trivializations. Both maps are supplied so inversion is
smooth on the chart domain without invoking a general inverse theorem. -/
structure TangentFrameGauge (I : ModelWithCorners ℝ E H)
    [IsManifold I 1 M] [IsManifold I (n + 1) M] where
  toFrame : atlas H M → M → E →L[ℝ] E
  fromFrame : atlas H M → M → E →L[ℝ] E
  to_from : ∀ i x, x ∈ (tangentBundleCore I M).baseSet i →
    ∀ v, toFrame i x (fromFrame i x v) = v
  from_to : ∀ i x, x ∈ (tangentBundleCore I M).baseSet i →
    ∀ v, fromFrame i x (toFrame i x v) = v
  smooth_to : ∀ i, ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) n (toFrame i)
    ((tangentBundleCore I M).baseSet i)
  smooth_from : ∀ i, ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) n (fromFrame i)
    ((tangentBundleCore I M).baseSet i)

namespace TangentFrameGauge

variable (F : TangentFrameGauge I (M := M) (n := n))

/-- The transition between adapted tangent frames is derived from the
manifold's chart derivative and the two frame gauges. -/
def coordChange (i j : atlas H M) (x : M) : E →L[ℝ] E :=
  (F.toFrame j x).comp
    (((tangentBundleCore I M).coordChange i j x).comp (F.fromFrame i x))

theorem coordChange_apply (i j : atlas H M) (x : M) (v : E) :
    F.coordChange i j x v =
      F.toFrame j x ((tangentBundleCore I M).coordChange i j x
        (F.fromFrame i x v)) := rfl

theorem coordChange_self (i : atlas H M) (x : M)
    (hx : x ∈ (tangentBundleCore I M).baseSet i) (v : E) :
    F.coordChange i i x v = v := by
  rw [coordChange_apply, (tangentBundleCore I M).coordChange_self i x hx]
  exact F.to_from i x hx v

theorem coordChange_comp (i j k : atlas H M) (x : M)
    (hi : x ∈ (tangentBundleCore I M).baseSet i)
    (hj : x ∈ (tangentBundleCore I M).baseSet j)
    (hk : x ∈ (tangentBundleCore I M).baseSet k) (v : E) :
    F.coordChange j k x (F.coordChange i j x v) = F.coordChange i k x v := by
  simp only [coordChange_apply]
  rw [F.from_to j x hj]
  rw [(tangentBundleCore I M).coordChange_comp i j k x ⟨⟨hi, hj⟩, hk⟩]

theorem continuousOn_coordChange (i j : atlas H M) :
    ContinuousOn (F.coordChange i j)
      ((tangentBundleCore I M).baseSet i ∩ (tangentBundleCore I M).baseSet j) := by
  have hto : ContinuousOn (F.toFrame j)
      ((tangentBundleCore I M).baseSet i ∩ (tangentBundleCore I M).baseSet j) :=
    (F.smooth_to j).continuousOn.mono Set.inter_subset_right
  have hfrom : ContinuousOn (F.fromFrame i)
      ((tangentBundleCore I M).baseSet i ∩ (tangentBundleCore I M).baseSet j) :=
    (F.smooth_from i).continuousOn.mono Set.inter_subset_left
  have hcore := (tangentBundleCore I M).continuousOn_coordChange i j
  exact hto.clm_comp (hcore.clm_comp hfrom)

/-- A new core on the same manifold, with coordinates in the adapted tangent
frames. Its cocycle is proved from the actual tangent chart derivatives. -/
def adaptedCore : VectorBundleCore ℝ M E (atlas H M) where
  baseSet := (tangentBundleCore I M).baseSet
  isOpen_baseSet := (tangentBundleCore I M).isOpen_baseSet
  indexAt := (tangentBundleCore I M).indexAt
  mem_baseSet_at := (tangentBundleCore I M).mem_baseSet_at
  coordChange := F.coordChange
  coordChange_self := F.coordChange_self
  continuousOn_coordChange := F.continuousOn_coordChange
  coordChange_comp i j k x hx v :=
    F.coordChange_comp i j k x hx.1.1 hx.1.2 hx.2 v

theorem smooth_coordChange (i j : atlas H M) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) n (F.coordChange i j)
      ((tangentBundleCore I M).baseSet i ∩ (tangentBundleCore I M).baseSet j) := by
  have hto : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) n (F.toFrame j)
      ((tangentBundleCore I M).baseSet i ∩ (tangentBundleCore I M).baseSet j) :=
    (F.smooth_to j).mono Set.inter_subset_right
  have hfrom : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) n (F.fromFrame i)
      ((tangentBundleCore I M).baseSet i ∩ (tangentBundleCore I M).baseSet j) :=
    (F.smooth_from i).mono Set.inter_subset_left
  haveI : (tangentBundleCore I M).IsContMDiff I n := tangentBundleCore.isContMDiff
  have hcore := (tangentBundleCore I M).contMDiffOn_coordChange (n := n) I i j
  exact hto.clm_comp (hcore.clm_comp hfrom)

instance adaptedCore_isContMDiff : F.adaptedCore.IsContMDiff I n where
  contMDiffOn_coordChange := F.smooth_coordChange

/-- The adapted tangent core is a smooth vector bundle over the original
manifold, with the differentiability order inherited from its frame gauges. -/
def adaptedVectorBundle : ContMDiffVectorBundle n E F.adaptedCore.Fiber I :=
  F.adaptedCore.instContMDiffVectorBundle

/-- The adapted bundle's preferred fiber coordinates are converted back to
the actual tangent fiber coordinates by the inverse local frame. -/
def toTangentTotal : F.adaptedCore.TotalSpace → TangentBundle I M :=
  fun p => ⟨p.1, F.fromFrame ((tangentBundleCore I M).indexAt p.1) p.1 p.2⟩

/-- The inverse coordinate conversion on the genuine tangent bundle. -/
def fromTangentTotal : TangentBundle I M → F.adaptedCore.TotalSpace :=
  fun p => ⟨p.1, F.toFrame ((tangentBundleCore I M).indexAt p.1) p.1 p.2⟩

@[simp] theorem fromTangent_toTangent (p : F.adaptedCore.TotalSpace) :
    F.fromTangentTotal (F.toTangentTotal p) = p := by
  cases p with
  | mk x v =>
    apply Bundle.TotalSpace.ext
    · rfl
    · exact heq_of_eq (F.to_from _ x ((tangentBundleCore I M).mem_baseSet_at x) v)

@[simp] theorem toTangent_fromTangent (p : TangentBundle I M) :
    F.toTangentTotal (F.fromTangentTotal p) = p := by
  cases p with
  | mk x v =>
    apply Bundle.TotalSpace.ext
    · rfl
    · exact heq_of_eq (F.from_to _ x ((tangentBundleCore I M).mem_baseSet_at x) v)

theorem toTangent_localTriv (i : atlas H M) (p : F.adaptedCore.TotalSpace)
    (hp : p.1 ∈ (tangentBundleCore I M).baseSet i) :
    ((tangentBundleCore I M).localTriv i (F.toTangentTotal p)).2 =
      F.fromFrame i p.1 ((F.adaptedCore.localTriv i p).2) := by
  change (tangentBundleCore I M).coordChange
      ((tangentBundleCore I M).indexAt p.1) i p.1
      (F.fromFrame ((tangentBundleCore I M).indexAt p.1) p.1 p.2) =
    F.fromFrame i p.1 (F.coordChange
      ((tangentBundleCore I M).indexAt p.1) i p.1 p.2)
  rw [F.coordChange_apply, F.from_to i p.1 hp]

theorem fromTangent_localTriv (i : atlas H M) (p : TangentBundle I M)
    (_hp : p.1 ∈ (tangentBundleCore I M).baseSet i) :
    ((F.adaptedCore.localTriv i) (F.fromTangentTotal p)).2 =
      F.toFrame i p.1 (((tangentBundleCore I M).localTriv i p).2) := by
  change F.coordChange ((tangentBundleCore I M).indexAt p.1) i p.1
      (F.toFrame ((tangentBundleCore I M).indexAt p.1) p.1 p.2) =
    F.toFrame i p.1 ((tangentBundleCore I M).coordChange
      ((tangentBundleCore I M).indexAt p.1) i p.1 p.2)
  rw [F.coordChange_apply,
    F.from_to _ p.1 ((tangentBundleCore I M).mem_baseSet_at p.1)]

/-- The frame conversion is continuous as a map between the constructed
adapted bundle and mathlib's genuine tangent bundle. -/
theorem continuous_toTangentTotal : Continuous F.toTangentTotal := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let i := (tangentBundleCore I M).indexAt p.1
  let s : Set F.adaptedCore.TotalSpace :=
    (F.adaptedCore.localTriv i).source
  have hs : IsOpen s := (F.adaptedCore.localTriv i).open_source
  have hp : p ∈ s := by
    exact (F.adaptedCore.mem_localTriv_source i p).mpr
      ((tangentBundleCore I M).mem_baseSet_at p.1)
  have hproj : Continuous F.adaptedCore.proj := F.adaptedCore.continuous_proj
  have hfrom : ContinuousOn (fun q : F.adaptedCore.TotalSpace => F.fromFrame i q.1) s := by
    apply (F.smooth_from i).continuousOn.comp hproj.continuousOn
    intro q hq
    exact (F.adaptedCore.mem_localTriv_source i q).mp hq
  have hcoord : ContinuousOn (fun q : F.adaptedCore.TotalSpace =>
      ((F.adaptedCore.localTriv i) q).2) s :=
    (F.adaptedCore.localTriv i).continuousOn.snd
  have happly : ContinuousAt (fun q : F.adaptedCore.TotalSpace =>
      F.fromFrame i q.1 ((F.adaptedCore.localTriv i q).2)) p :=
    (hfrom.clm_apply hcoord).continuousAt (hs.mem_nhds hp)
  have heq : (fun q : F.adaptedCore.TotalSpace =>
      ((tangentBundleCore I M).localTriv i (F.toTangentTotal q)).2) =ᶠ[𝓝 p]
      (fun q => F.fromFrame i q.1 ((F.adaptedCore.localTriv i q).2)) := by
    filter_upwards [hs.mem_nhds hp] with q hq
    exact F.toTangent_localTriv i q ((F.adaptedCore.mem_localTriv_source i q).mp hq)
  have htarget := happly.congr_of_eventuallyEq heq
  apply (FiberBundle.continuousAt_totalSpace E F.toTangentTotal).2
  constructor
  · exact hproj.continuousAt
  · simpa only [TangentBundle.trivializationAt_eq_localTriv] using htarget

theorem continuous_fromTangentTotal : Continuous F.fromTangentTotal := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let i := (tangentBundleCore I M).indexAt p.1
  let s : Set (TangentBundle I M) := ((tangentBundleCore I M).localTriv i).source
  have hs : IsOpen s := ((tangentBundleCore I M).localTriv i).open_source
  have hp : p ∈ s := by
    exact ((tangentBundleCore I M).mem_localTriv_source i p).mpr
      ((tangentBundleCore I M).mem_baseSet_at p.1)
  have hproj : Continuous (tangentBundleCore I M).proj :=
    (tangentBundleCore I M).continuous_proj
  have hto : ContinuousOn (fun q : TangentBundle I M => F.toFrame i q.1) s := by
    apply (F.smooth_to i).continuousOn.comp hproj.continuousOn
    intro q hq
    exact ((tangentBundleCore I M).mem_localTriv_source i q).mp hq
  have hcoord : ContinuousOn (fun q : TangentBundle I M =>
      (((tangentBundleCore I M).localTriv i) q).2) s :=
    ((tangentBundleCore I M).localTriv i).continuousOn.snd
  have happly : ContinuousAt (fun q : TangentBundle I M =>
      F.toFrame i q.1 (((tangentBundleCore I M).localTriv i q).2)) p :=
    (hto.clm_apply hcoord).continuousAt (hs.mem_nhds hp)
  have heq : (fun q : TangentBundle I M =>
      ((F.adaptedCore.localTriv i) (F.fromTangentTotal q)).2) =ᶠ[𝓝 p]
      (fun q => F.toFrame i q.1 (((tangentBundleCore I M).localTriv i q).2)) := by
    filter_upwards [hs.mem_nhds hp] with q hq
    exact F.fromTangent_localTriv i q
      (((tangentBundleCore I M).mem_localTriv_source i q).mp hq)
  have htarget := happly.congr_of_eventuallyEq heq
  apply (FiberBundle.continuousAt_totalSpace E F.fromTangentTotal).2
  constructor
  · exact hproj.continuousAt
  · simpa only [F.adaptedCore.trivializationAt] using htarget

/-- The adapted frame bundle is topologically equivalent to the genuine
tangent bundle; both maps preserve the base point and are fiberwise linear. -/
def tangentHomeomorph : F.adaptedCore.TotalSpace ≃ₜ TangentBundle I M where
  toFun := F.toTangentTotal
  invFun := F.fromTangentTotal
  left_inv := F.fromTangent_toTangent
  right_inv := F.toTangent_fromTangent
  continuous_toFun := F.continuous_toTangentTotal
  continuous_invFun := F.continuous_fromTangentTotal

/-- Each adapted fiber is continuously linearly equivalent to the genuine
tangent fiber at that point. -/
def tangentFiberEquiv (x : M) : F.adaptedCore.Fiber x ≃L[ℝ] TangentSpace I x where
  toFun := F.fromFrame ((tangentBundleCore I M).indexAt x) x
  invFun := F.toFrame ((tangentBundleCore I M).indexAt x) x
  map_add' := by intros; simp
  map_smul' := by intros; simp
  left_inv := F.to_from _ x ((tangentBundleCore I M).mem_baseSet_at x)
  right_inv := F.from_to _ x ((tangentBundleCore I M).mem_baseSet_at x)
  continuous_toFun := (F.fromFrame _ x).continuous
  continuous_invFun := (F.toFrame _ x).continuous

end TangentFrameGauge

/-- A smooth almost-quaternionic reduction of the tangent bundle in adapted
local frames. The compatibility is preservation of the quaternionic span,
not preservation of any chosen `I,J,K` triple. -/
structure SmoothAlmostQuaternionicTangent where
  frames : TangentFrameGauge I (M := M) (n := n)
  reduction : VectorBundleFrameTransitions.QuaternionicFrameReduction frames.adaptedCore

namespace SmoothAlmostQuaternionicTangent

variable (Q : SmoothAlmostQuaternionicTangent (I := I) (M := M) (n := n))

/-- The local triple viewed in the original tangent chart coordinates.
Unlike the triple in an adapted frame, this depends smoothly on the point. -/
def chartGenerator (i : atlas H M) (t : Fin 3) (x : M) : E →L[ℝ] E :=
  (Q.frames.fromFrame i x).comp
    ((VectorBundleFrameTransitions.quaternionicGenerator (Q.reduction.Q i) t).comp
      (Q.frames.toFrame i x))

theorem smooth_chartGenerator (i : atlas H M) (t : Fin 3) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) n (Q.chartGenerator i t)
      ((tangentBundleCore I M).baseSet i) := by
  have hconst : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) n
      (fun _ : M => VectorBundleFrameTransitions.quaternionicGenerator (Q.reduction.Q i) t)
      ((tangentBundleCore I M).baseSet i) := contMDiffOn_const
  exact (Q.frames.smooth_from i).clm_comp (hconst.clm_comp (Q.frames.smooth_to i))

/-- Conjugation from an adapted frame back to the ordinary tangent chart. -/
def chartConjugation (i : atlas H M) (x : M) :
    (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  ((ContinuousLinearMap.mul ℝ (E →L[ℝ] E)) (Q.frames.fromFrame i x)).comp
    (((ContinuousLinearMap.mul ℝ (E →L[ℝ] E)).flip) (Q.frames.toFrame i x))

theorem chartConjugation_apply (i : atlas H M) (x : M) (a : E →L[ℝ] E) :
    Q.chartConjugation i x a =
      Q.frames.fromFrame i x * a * Q.frames.toFrame i x := by
  change Q.frames.fromFrame i x * (a * Q.frames.toFrame i x) = _
  rw [mul_assoc]

theorem chartGenerator_eq_chartConjugation (i : atlas H M) (x : M) (t : Fin 3) :
    Q.chartGenerator i t x = Q.chartConjugation i x
      (VectorBundleFrameTransitions.quaternionicGenerator (Q.reduction.Q i) t) := by
  ext v
  rfl

/-- The quaternionic subspace written in the ordinary tangent chart. -/
def chartSpan (i : atlas H M) (x : M) : Submodule ℝ (E →L[ℝ] E) :=
  Submodule.span ℝ (Set.range (fun t : Fin 3 => Q.chartGenerator i t x))

theorem chartSpan_eq_map (i : atlas H M) (x : M) :
    Q.chartSpan i x = Submodule.map (Q.chartConjugation i x).toLinearMap
      (VectorBundleFrameTransitions.quaternionicSpan (Q.reduction.Q i)) := by
  rw [chartSpan, VectorBundleFrameTransitions.quaternionicSpan, Submodule.map_span]
  congr 1
  ext a
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, ⟨t, rfl⟩, (Q.chartGenerator_eq_chartConjugation i x t).symm⟩
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, (Q.chartGenerator_eq_chartConjugation i x t).symm⟩

theorem chartConjugation_injective (i : atlas H M) (x : M)
    (hi : x ∈ (tangentBundleCore I M).baseSet i) :
    Function.Injective (Q.chartConjugation i x) := by
  have hfi : Q.frames.toFrame i x * Q.frames.fromFrame i x = 1 := by
    ext v
    exact Q.frames.to_from i x hi v
  have hleft (a : E →L[ℝ] E) :
      Q.frames.toFrame i x * (Q.chartConjugation i x a) *
        Q.frames.fromFrame i x = a := by
    rw [Q.chartConjugation_apply]
    simp only [mul_assoc]
    rw [← mul_assoc (Q.frames.toFrame i x) (Q.frames.fromFrame i x), hfi]
    simp only [one_mul, mul_one]
  intro a b hab
  calc
    a = Q.frames.toFrame i x * Q.chartConjugation i x a * Q.frames.fromFrame i x :=
      (hleft a).symm
    _ = Q.frames.toFrame i x * Q.chartConjugation i x b * Q.frames.fromFrame i x := by
      rw [hab]
    _ = b := hleft b

theorem chartGenerator_linearIndependent [Nontrivial E] (i : atlas H M) (x : M)
    (hi : x ∈ (tangentBundleCore I M).baseSet i) :
    LinearIndependent ℝ (fun t : Fin 3 => Q.chartGenerator i t x) := by
  have h := (VectorBundleFrameTransitions.quaternionicGenerator_linearIndependent
    (Q.reduction.Q i)).map' (Q.chartConjugation i x).toLinearMap
      (LinearMap.ker_eq_bot_of_injective (Q.chartConjugation_injective i x hi))
  convert h using 1

theorem finrank_chartSpan [Nontrivial E] (i : atlas H M) (x : M)
    (hi : x ∈ (tangentBundleCore I M).baseSet i) :
    Module.finrank ℝ (Q.chartSpan i x) = 3 := by
  change Module.finrank ℝ
    (Submodule.span ℝ (Set.range (fun t : Fin 3 => Q.chartGenerator i t x))) = 3
  simpa using finrank_span_eq_card (Q.chartGenerator_linearIndependent i x hi)

theorem tangent_adjoint_chartConjugation (i j : atlas H M) (x : M)
    (hj : x ∈ (tangentBundleCore I M).baseSet j) (a : E →L[ℝ] E) :
    (VectorBundleFrameTransitions.transitionAtlas (tangentBundleCore I M)).adjointCoordChange
        i j x (Q.chartConjugation i x a) =
      Q.chartConjugation j x
        ((VectorBundleFrameTransitions.transitionAtlas Q.frames.adaptedCore).adjointCoordChange
          i j x a) := by
  rw [VectorBundleFrameTransitions.adjointCoordChange_apply,
    VectorBundleFrameTransitions.adjointCoordChange_apply,
    Q.chartConjugation_apply, Q.chartConjugation_apply]
  have hfj : Q.frames.fromFrame j x * Q.frames.toFrame j x = 1 := by
    ext v
    exact Q.frames.from_to j x hj v
  change (tangentBundleCore I M).coordChange i j x *
      (Q.frames.fromFrame i x * a * Q.frames.toFrame i x) *
      (tangentBundleCore I M).coordChange j i x =
    Q.frames.fromFrame j x *
      ((Q.frames.toFrame j x * (tangentBundleCore I M).coordChange i j x *
        Q.frames.fromFrame i x) * a *
        (Q.frames.toFrame i x * (tangentBundleCore I M).coordChange j i x *
          Q.frames.fromFrame j x)) * Q.frames.toFrame j x
  simp only [mul_assoc]
  rw [← mul_assoc (Q.frames.fromFrame j x) (Q.frames.toFrame j x), hfj]
  simp only [one_mul, mul_one]

/-- A chart generator is carried into the next chart's quaternionic span by
the actual tangent transition derivative. -/
theorem tangent_generator_transport (i j : atlas H M) (x : M)
    (hi : x ∈ (tangentBundleCore I M).baseSet i)
    (hj : x ∈ (tangentBundleCore I M).baseSet j) (t : Fin 3) :
    (VectorBundleFrameTransitions.transitionAtlas (tangentBundleCore I M)).adjointCoordChange
      i j x (Q.chartGenerator i t x) ∈ Q.chartSpan j x := by
  rw [Q.chartGenerator_eq_chartConjugation,
    Q.tangent_adjoint_chartConjugation i j x hj,
    Q.chartSpan_eq_map]
  exact ⟨_, Q.reduction.generator_transport i j x hi hj t, rfl⟩

theorem tangent_map_chartSpan_le (i j : atlas H M) (x : M)
    (hi : x ∈ (tangentBundleCore I M).baseSet i)
    (hj : x ∈ (tangentBundleCore I M).baseSet j) :
    Submodule.map
      ((VectorBundleFrameTransitions.transitionAtlas (tangentBundleCore I M)).adjointCoordChange
        i j x).toLinearMap (Q.chartSpan i x) ≤ Q.chartSpan j x := by
  rw [chartSpan, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  exact Q.tangent_generator_transport i j x hi hj t

/-- The quaternionic endomorphism subspaces agree on tangent-chart overlaps;
in particular the locally smooth triples are allowed to rotate. -/
theorem tangent_map_chartSpan_eq (i j : atlas H M) (x : M)
    (hi : x ∈ (tangentBundleCore I M).baseSet i)
    (hj : x ∈ (tangentBundleCore I M).baseSet j) :
    Submodule.map
      ((VectorBundleFrameTransitions.transitionAtlas (tangentBundleCore I M)).adjointCoordChange
        i j x).toLinearMap (Q.chartSpan i x) = Q.chartSpan j x := by
  let P := VectorBundleFrameTransitions.transitionAtlas (tangentBundleCore I M)
  apply le_antisymm (Q.tangent_map_chartSpan_le i j x hi hj)
  intro a ha
  have hback : P.adjointCoordChange j i x a ∈ Q.chartSpan i x := by
    apply Q.tangent_map_chartSpan_le j i x hj hi
    exact ⟨a, ha, rfl⟩
  refine ⟨P.adjointCoordChange j i x a, hback, ?_⟩
  calc
    P.adjointCoordChange i j x (P.adjointCoordChange j i x a) =
      P.adjointCoordChange j j x a := P.adjointCoordChange_comp j i j x hj hi hj a
    _ = a := P.adjointCoordChange_self j x hj a

/-- The tangent reduction inherits the continuous rank-three bundle built
from its actual adapted tangent transitions. -/
def quaternionicRankThreeCore [Nontrivial E] [FiniteDimensional ℝ E] :
    VectorBundleCore ℝ M (Fin 3 → ℝ) (atlas H M) :=
  Q.reduction.rankThreeCore

/-- Every fixed coefficient vector has a smooth image under the rank-three
transition. This is the pointwise smoothness ingredient for its operator-valued
coordinate change. -/
theorem smooth_rankThreeCoordChange_apply [Nontrivial E] [FiniteDimensional ℝ E]
    (i j : atlas H M) (a : Fin 3 → ℝ) :
    ContMDiffOn I 𝓘(ℝ, Fin 3 → ℝ) n
      (fun x => Q.reduction.rankThreeCoordChange i j x a)
      (Q.frames.adaptedCore.baseSet i ∩ Q.frames.adaptedCore.baseSet j) := by
  let Z := Q.frames.adaptedCore
  let s := Z.baseSet i ∩ Z.baseSet j
  have h₁ : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) n (Z.coordChange i j) s :=
    Q.frames.smooth_coordChange i j
  have h₂ : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) n (Z.coordChange j i) s := by
    simpa only [s, Set.inter_comm] using Q.frames.smooth_coordChange j i
  have hconst : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) n
      (fun _ : M => VectorBundleFrameTransitions.QuaternionicFrameReduction.synth
        (Q.reduction.Q i) a) s := contMDiffOn_const
  have hmid : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) n
      (fun x => (VectorBundleFrameTransitions.QuaternionicFrameReduction.synth
        (Q.reduction.Q i) a).comp (Z.coordChange j i x)) s :=
    hconst.clm_comp h₂
  have hconj : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) n
      (fun x => (Z.coordChange i j x).comp
        ((VectorBundleFrameTransitions.QuaternionicFrameReduction.synth
          (Q.reduction.Q i) a).comp (Z.coordChange j i x))) s :=
    h₁.clm_comp hmid
  have hcoeff : ContMDiffOn I 𝓘(ℝ, (E →L[ℝ] E) →L[ℝ] (Fin 3 → ℝ)) n
      (fun _ : M => VectorBundleFrameTransitions.QuaternionicFrameReduction.coeff
        (Q.reduction.Q j)) s := contMDiffOn_const
  refine (hcoeff.clm_apply hconj).congr ?_
  intro x hx
  rw [Q.reduction.rankThreeCoordChange_apply,
    VectorBundleFrameTransitions.adjointCoordChange_apply]
  rfl

private def rankThreeOperatorEval :
    ((Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) ≃L[ℝ]
      (Fin 3 → Fin 3 → ℝ) :=
  (((LinearMap.toContinuousLinearMap (𝕜 := ℝ)
    (E := Fin 3 → ℝ) (F' := Fin 3 → ℝ)).symm).trans
      (((Pi.basisFun ℝ (Fin 3)).constr ℝ).symm)).toContinuousLinearEquiv

private theorem rankThreeOperatorEval_apply
    (T : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) (t : Fin 3) :
    rankThreeOperatorEval T t = T (Pi.basisFun ℝ (Fin 3) t) := rfl

theorem smooth_rankThreeCoordChange [Nontrivial E] [FiniteDimensional ℝ E]
    (i j : atlas H M) :
    ContMDiffOn I 𝓘(ℝ, (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) n
      (Q.reduction.rankThreeCoordChange i j)
      (Q.frames.adaptedCore.baseSet i ∩ Q.frames.adaptedCore.baseSet j) := by
  have hpi : ContMDiffOn I 𝓘(ℝ, Fin 3 → Fin 3 → ℝ) n
      (fun x => rankThreeOperatorEval (Q.reduction.rankThreeCoordChange i j x))
      (Q.frames.adaptedCore.baseSet i ∩ Q.frames.adaptedCore.baseSet j) := by
    apply contMDiffOn_pi_space.mpr
    intro t
    simpa only [rankThreeOperatorEval_apply] using
      Q.smooth_rankThreeCoordChange_apply i j (Pi.basisFun ℝ (Fin 3) t)
  have h := rankThreeOperatorEval.symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn hpi
  simpa [Function.comp_def] using h

instance quaternionicRankThreeCore_isContMDiff [Nontrivial E] [FiniteDimensional ℝ E] :
    Q.quaternionicRankThreeCore.IsContMDiff I n where
  contMDiffOn_coordChange := Q.smooth_rankThreeCoordChange

/-- The associated quaternionic rank-three bundle is smooth over the same
manifold, with transition regularity inherited from the adapted tangent
frames. -/
def quaternionicRankThreeVectorBundle [Nontrivial E] [FiniteDimensional ℝ E] :
    ContMDiffVectorBundle n (Fin 3 → ℝ) Q.quaternionicRankThreeCore.Fiber I :=
  Q.quaternionicRankThreeCore.instContMDiffVectorBundle



end SmoothAlmostQuaternionicTangent

end
end QuaternionicSymmetry.ManifoldQuaternionicReduction
