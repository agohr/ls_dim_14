import QuaternionicSymmetry.ManifoldFiniteDimensionalCLMSmooth
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Pull back a fixed positive bilinear metric through the genuine derivative
of a smooth immersion into a real normed vector space. The construction
retains the manifold's tangent topology and proves tensor smoothness. -/

namespace QuaternionicSymmetry.ManifoldImmersionPullbackMetric

open Bundle Manifold ManifoldFiniteDimensionalCLMSmooth
open scoped Manifold ContDiff Topology
noncomputable section

variable {E V M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (f : M → V) (g : V →L[ℝ] V →L[ℝ] ℝ)

-- Tangent fibers are definitionally the model space, but Mathlib hides
-- their norm instances to avoid accidental global inference.
private local instance (x : M) : NormedAddCommGroup (TangentSpace 𝓘(ℝ,E) x) := by
  change NormedAddCommGroup E
  infer_instance

private local instance (x : M) : NormedSpace ℝ (TangentSpace 𝓘(ℝ,E) x) := by
  change NormedSpace ℝ E
  infer_instance

private local instance (z : V) : NormedAddCommGroup (TangentSpace 𝓘(ℝ,V) z) := by
  change NormedAddCommGroup V
  infer_instance

private local instance (z : V) : NormedSpace ℝ (TangentSpace 𝓘(ℝ,V) z) := by
  change NormedSpace ℝ V
  infer_instance

private local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) x) := by
  change FiniteDimensional ℝ E
  infer_instance

private abbrev B := E →L[ℝ] E →L[ℝ] ℝ

/-- The literal pullback bilinear form, evaluated on actual tangent vectors. -/
def metricCLM (x : M) :
    TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ :=
  let D := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x
  ((ContinuousLinearMap.compL ℝ (TangentSpace 𝓘(ℝ,E) x) V ℝ).flip D).comp
    (g.comp D)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem metricCLM_apply (x : M) (v w : TangentSpace 𝓘(ℝ,E) x) :
    metricCLM (E := E) f g x v w =
      g (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x v)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x w) := rfl

private abbrev tangentTriv (x : M) :=
  trivializationAt E (TangentSpace 𝓘(ℝ,E)) x

private abbrev metricTriv (x : M) :=
  trivializationAt (B (E := E))
    (fun y : M => TangentSpace 𝓘(ℝ,E) y →L[ℝ]
      TangentSpace 𝓘(ℝ,E) y →L[ℝ] ℝ) x

private def frameField (x : M) (a : E) (y : M) : TangentSpace 𝓘(ℝ,E) y :=
  (tangentTriv (E := E) x).symmL ℝ y a

omit [FiniteDimensional ℝ E] in
private theorem frameField_smoothOn (x : M) (a : E) :
    ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E).tangent ∞
      (fun y => (⟨y,frameField (E := E) x a y⟩ : TangentBundle 𝓘(ℝ,E) M))
      (tangentTriv (E := E) x).baseSet := by
  let e := tangentTriv (E := E) x
  letI : MemTrivializationAtlas e := by
    dsimp [e, tangentTriv]
    infer_instance
  have hp : ContMDiffOn 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (fun y : M => (y,a)) e.baseSet :=
    contMDiffOn_id.prodMk contMDiffOn_const
  have hm : Set.MapsTo (fun y : M => (y,a)) e.baseSet e.target :=
    fun y hy => e.mem_target.mpr hy
  apply (e.contMDiffOn_symm.comp hp hm).congr
  intro y hy
  have he := e.symm_apply_eq_mk_continuousLinearEquivAt_symm (R := ℝ) y hy a
  simpa only [frameField,
    e.symm_continuousLinearEquivAt_eq (R := ℝ) hy] using he.symm

private def metricCoordinates (x y : M) : B (E := E) :=
  ((metricTriv (E := E) x) ⟨y,metricCLM (E := E) f g y⟩).2

omit [FiniteDimensional ℝ E] in
private theorem metricCoordinates_apply (x y : M)
    (hy : y ∈ (tangentTriv (E := E) x).baseSet) (a b : E) :
    metricCoordinates (E := E) f g x y a b =
      metricCLM (E := E) f g y (frameField (E := E) x a y)
        (frameField (E := E) x b y) := by
  change (trivializationAt (B (E := E))
    (fun y : M => TangentSpace 𝓘(ℝ,E) y →L[ℝ]
      TangentSpace 𝓘(ℝ,E) y →L[ℝ] ℝ) x ⟨y,metricCLM (E := E) f g y⟩).2 a b = _
  rw [hom_trivializationAt_apply (σ := RingHom.id ℝ)
    (F₁ := E) (E₁ := TangentSpace 𝓘(ℝ,E))
    (F₂ := E →L[ℝ] ℝ)
    (E₂ := fun y : M => TangentSpace 𝓘(ℝ,E) y →L[ℝ] ℝ)]
  rw [inCoordinates_apply_eq₂ (h₁x := hy) (h₂x := hy) (h₃x := by simp)]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq, frameField, tangentTriv, Trivialization.symmL]
  rfl

/-- Smoothness of the pullback tensor follows from the tangent map and
local constant-frame evaluations; it is not an extra metric premise. -/
theorem metricCLM_contMDiff (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ f) :
    ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,B (E := E))) ∞
      (fun x : M => (⟨x,metricCLM (E := E) f g x⟩ : TotalSpace (B (E := E))
        (fun x : M => TangentSpace 𝓘(ℝ,E) x →L[ℝ]
          TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ))) := by
  intro x
  let U := (tangentTriv (E := E) x).baseSet
  have hU : IsOpen U := (tangentTriv (E := E) x).open_baseSet
  have hx : x ∈ U := mem_baseSet_trivializationAt _ _ _
  have hd (a : E) : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,V) ∞
      (fun y => mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f y (frameField (E := E) x a y)) U := by
    have ht := (hf.contMDiff_tangentMap (m := ∞) (by simp)).comp_contMDiffOn
      (frameField_smoothOn (E := E) x a)
    exact (contMDiff_snd_tangentBundle_modelSpace V 𝓘(ℝ,V)).comp_contMDiffOn ht
  have hcoord : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,B (E := E)) ∞
      (metricCoordinates (E := E) f g x) U := by
    apply (contMDiffOn_clm_apply_iff (I := 𝓘(ℝ,E)) hU).mpr
    intro a
    apply (contMDiffOn_clm_apply_iff (I := 𝓘(ℝ,E)) hU).mpr
    intro b
    apply ((contMDiffOn_const.clm_apply (hd a)).clm_apply (hd b)).congr
    intro y hy
    exact metricCoordinates_apply (E := E) f g x y hy a b
  rw [contMDiffAt_section]
  simpa only [metricCoordinates, metricTriv] using
    ((hcoord x hx).contMDiffAt (hU.mem_nhds hx))

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
/-- Injectivity of the genuine derivative transfers boundedness of the
ambient metric ball to each tangent fiber in its existing topology. -/
theorem metricCLM_isVonNBounded
    (hg : Bornology.IsVonNBounded ℝ {v : V | g v v < 1})
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x)) (x : M) :
    Bornology.IsVonNBounded ℝ
      {v : TangentSpace 𝓘(ℝ,E) x | metricCLM (E := E) f g x v v < 1} := by
  let D := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x
  obtain ⟨K, _, hK⟩ := D.toLinearMap.injective_iff_antilipschitz.mp (hi x)
  change Bornology.IsVonNBounded ℝ (D ⁻¹' {v : V | g v v < 1})
  rw [NormedSpace.isVonNBounded_iff] at hg ⊢
  exact hK.isBounded_preimage hg

/-- The actual smooth pullback Riemannian metric. All ambient metric
properties are explicit; smoothness and topology compatibility of its
pullback are proved internally. -/
def smoothMetric
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ f)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x))
    (hsymm : ∀ v w, g v w = g w v)
    (hpos : ∀ v, v ≠ 0 → 0 < g v v)
    (hbound : Bornology.IsVonNBounded ℝ {v : V | g v v < 1}) :
    Bundle.ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (TangentSpace 𝓘(ℝ,E) : M → Type _) where
  inner := metricCLM (E := E) f g
  symm := fun x v w => hsymm _ _
  pos := by
    intro x v hv
    apply hpos
    intro h
    apply hv
    exact hi x (h.trans (map_zero (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x)).symm)
  isVonNBounded := metricCLM_isVonNBounded (E := E) f g hbound hi
  contMDiff := metricCLM_contMDiff (E := E) f g hf

end
end QuaternionicSymmetry.ManifoldImmersionPullbackMetric
