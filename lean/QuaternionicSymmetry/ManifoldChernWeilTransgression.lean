import QuaternionicSymmetry.ManifoldChernWeilGluing
import QuaternionicSymmetry.LocalChernWeilOrderedExact

/-!
Global exact transgression for chart-compatible local connection paths.
The ordered local Chern--Simons formula supplies the derivative identity;
gluing its primitive requires its own actual chart transition law.
-/

namespace QuaternionicSymmetry.ManifoldChernWeilTransgression

open QuaternionicSymmetry.ManifoldDifferentialForms
  QuaternionicSymmetry.ManifoldChartFormGluing
  QuaternionicSymmetry.ManifoldChernWeilGluing
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalChernWeilOrderedTransgression
  QuaternionicSymmetry.LocalChernWeilOrderedExact
  QuaternionicSymmetry.LocalConnection
open scoped Manifold Topology ContDiff

variable {E M V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

noncomputable section

local instance : NormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem cast_form_apply {a b : ℕ} (h : a = b)
    (alpha : Form 𝓘(ℝ, E) M a) (x : M) :
    (h ▸ alpha) x = h ▸ alpha x := by
  cases h
  rfl

private theorem cast_comp {a b : ℕ} (h : a = b)
    (eta : E [⋀^Fin a]→L[ℝ] ℝ) (L : E →L[ℝ] E) :
    (traceDegreeCast h eta).compContinuousLinearMap L =
      h ▸ eta.compContinuousLinearMap L := by
  cases h
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem cast_sub {a b : ℕ} (h : a = b)
    (alpha beta : Form 𝓘(ℝ, E) M a) :
    h ▸ (alpha - beta) = (h ▸ alpha) - (h ▸ beta) := by
  cases h
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem cast_symm {a b : ℕ} (h : a = b)
    (alpha : Form 𝓘(ℝ, E) M a) :
    h.symm ▸ (h ▸ alpha) = alpha := by
  cases h
  rfl

private theorem cast_closed_coe {a b : ℕ} (h : a = b)
    (alpha : closedForms (E := E) (M₀ := M) a) :
    (((h ▸ alpha : closedForms (E := E) (M₀ := M) b) :
      smoothForms (I := 𝓘(ℝ, E)) (M := M) (n := b)) :
      Form 𝓘(ℝ, E) M b) =
    h ▸ (alpha.1.1 : Form 𝓘(ℝ, E) M a) := by
  cases h
  rfl

/-- Two compatible local connection atlases joined by an affine path,
together with a compatible Chern--Simons primitive on actual chart overlaps. -/
structure TracePowerHomotopy (k : ℕ) where
  start : TracePowerAtlas (E := E) (M := M) (V := V) k
  finish : TracePowerAtlas (E := E) (M := M) (V := V) k
  direction : M → QuaternionicSymmetry.LocalConnection.Form
    (E := E) (A := V →L[ℝ] V)
  endpoint : ∀ p : M, finish.connection p =
    start.connection p + direction p
  directionC2 : ∀ (p : M) (y : E),
    y ∈ (extChartAt 𝓘(ℝ, E) p).target →
      ContDiffAt ℝ 2 (direction p) y
  primitiveRegular : ∀ p : M,
    ContDiffOn ℝ ∞
      (traceOrderedTransgressionForm
        QuaternionicSymmetry.LocalEndomorphismTrace.traceCLM
        (start.connection p) (direction p) k)
      (extChartAt 𝓘(ℝ, E) p).target
  primitiveCoordinateLaw : ∀ (p q : M) (y : E),
    y ∈ (extChartAt 𝓘(ℝ, E) p).target →
    (extChartAt 𝓘(ℝ, E) p).symm y ∈
      (extChartAt 𝓘(ℝ, E) q).source →
    traceOrderedTransgressionForm
      QuaternionicSymmetry.LocalEndomorphismTrace.traceCLM
      (start.connection p) (direction p) k y =
      ContinuousAlternatingMap.compContinuousLinearMap
        (traceOrderedTransgressionForm
          QuaternionicSymmetry.LocalEndomorphismTrace.traceCLM
          (start.connection q) (direction q) k
          ((extChartAt 𝓘(ℝ, E) q)
            ((extChartAt 𝓘(ℝ, E) p).symm y)))
        (fderiv ℝ
          ((extChartAt 𝓘(ℝ, E) q) ∘
            (extChartAt 𝓘(ℝ, E) p).symm) y)

namespace TracePowerHomotopy

variable {k : ℕ} (H : TracePowerHomotopy (E := E) (M := M) (V := V) k)

def primitiveChart : ChartFormData (E := E) (M := M) (primitiveDegree k) where
  localForm p := traceOrderedTransgressionForm
    QuaternionicSymmetry.LocalEndomorphismTrace.traceCLM
    (H.start.connection p) (H.direction p) k
  regular := H.primitiveRegular
  coordinateLaw := H.primitiveCoordinateLaw

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem local_exact (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    traceCurvaturePowerForm (H.finish.connection p) k y -
      traceCurvaturePowerForm (H.start.connection p) k y =
      traceDegreeCast (primitiveDegree_add_one k)
        (extDeriv (H.primitiveChart.localForm p) y) := by
  rw [H.endpoint p]
  exact traceCurvaturePowerForm_sub_eq_extDeriv_ordered
    (H.start.connection p) (H.direction p) k y
    (H.start.connectionC2 p y hy) (H.directionC2 p y hy)

/-- The chartwise ordered transgression is an exact equality of global
forms on the actual tangent bundle. -/
theorem global_exact :
    H.finish.globalForm - H.start.globalForm =
      (primitiveDegree_add_one k) ▸
        exteriorDerivative H.primitiveChart.toForm := by
  funext x
  let C := extChartAt 𝓘(ℝ, E) x
  have hy : C x ∈ C.target := mem_extChartAt_target x
  have hevent : inChartModel x H.primitiveChart.toForm =ᶠ[𝓝 (C x)]
      H.primitiveChart.localForm x := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hy] with y hy'
    exact H.primitiveChart.inChartModel_toForm x hy'
  have hderiv := hevent.extDeriv_eq
  have hlocal := H.local_exact x (C x) hy
  rw [cast_form_apply]
  change
    (traceCurvaturePowerForm (H.finish.connection x) k (C x)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C x) -
      (traceCurvaturePowerForm (H.start.connection x) k (C x)).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C x) =
      (primitiveDegree_add_one k) ▸
        (extDeriv (inChartModel x H.primitiveChart.toForm) (C x)).compContinuousLinearMap
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C x)
  rw [hderiv]
  rw [← cast_comp (primitiveDegree_add_one k)]
  exact congrArg (fun eta => eta.compContinuousLinearMap
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C x)) hlocal

/-- The two global trace powers represent the same de Rham class. -/
theorem cohomologyClass_eq :
    QuotientAddGroup.mk
      ((primitiveDegree_add_one k).symm ▸ H.finish.closedGlobalForm) =
    (QuotientAddGroup.mk
      ((primitiveDegree_add_one k).symm ▸ H.start.closedGlobalForm) :
        positiveDegreeCohomology (E := E) (M₀ := M) (primitiveDegree k)) := by
  let h := primitiveDegree_add_one k
  have hform : (h.symm ▸ H.finish.globalForm) -
      (h.symm ▸ H.start.globalForm) =
        exteriorDerivative H.primitiveChart.toForm := by
    have hh := congrArg
      (fun f : Form 𝓘(ℝ, E) M (powerDegree k) => h.symm ▸ f)
      H.global_exact
    simpa only [cast_sub, cast_symm] using hh
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  change ((h.symm ▸ H.finish.closedGlobalForm) -
      (h.symm ▸ H.start.closedGlobalForm) :
        closedForms (E := E) (M₀ := M) (primitiveDegree k + 1)) ∈
    exactClosedAddSubgroup (E := E) (M₀ := M) (primitiveDegree k)
  change (((h.symm ▸ H.finish.closedGlobalForm) -
      (h.symm ▸ H.start.closedGlobalForm) :
        closedForms (E := E) (M₀ := M) (primitiveDegree k + 1)) :
        smoothForms (I := 𝓘(ℝ, E)) (M := M) (n := primitiveDegree k + 1)) ∈
    exactForms (E := E) (M₀ := M) (primitiveDegree k)
  refine ⟨⟨H.primitiveChart.toForm, H.primitiveChart.toForm_smooth⟩, ?_⟩
  apply Subtype.ext
  change exteriorDerivative H.primitiveChart.toForm =
    (((h.symm ▸ H.finish.closedGlobalForm :
      closedForms (E := E) (M₀ := M) (primitiveDegree k + 1)) :
      smoothForms (I := 𝓘(ℝ, E)) (M := M) (n := primitiveDegree k + 1)) :
      Form 𝓘(ℝ, E) M (primitiveDegree k + 1)) -
    (((h.symm ▸ H.start.closedGlobalForm :
      closedForms (E := E) (M₀ := M) (primitiveDegree k + 1)) :
      smoothForms (I := 𝓘(ℝ, E)) (M := M) (n := primitiveDegree k + 1)) :
      Form 𝓘(ℝ, E) M (primitiveDegree k + 1))
  rw [cast_closed_coe, cast_closed_coe]
  exact hform.symm

end TracePowerHomotopy
end
end QuaternionicSymmetry.ManifoldChernWeilTransgression
