import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
Scalar alternating forms on actual manifold tangent fibers. A form is a
section of the alternating cotangent bundle, not a function on a model space.
The pullback uses the manifold derivative on each tangent fiber.
-/

namespace QuaternionicSymmetry.ManifoldDifferentialForms

open Filter
open scoped Manifold ContDiff Topology

variable {E E' E'' H H' H'': Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {I'' : ModelWithCorners ℝ E'' H''}
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]
  [TopologicalSpace P] [ChartedSpace H'' P] {n : ℕ}

/-- A scalar differential form on the genuine tangent fibers of a manifold. -/
abbrev Form (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] (n : ℕ) : Type _ :=
  ∀ x : M, TangentSpace I x [⋀^Fin n]→L[ℝ] ℝ

/-- Tangent-map pullback of an alternating form. -/
noncomputable def formPullback (f : M → N) (alpha : Form I' N n) : Form I M n :=
  fun x => (alpha (f x)).compContinuousLinearMap (mfderiv I I' f x)

theorem formPullback_apply (f : M → N) (alpha : Form I' N n)
    (x : M) (v : Fin n → TangentSpace I x) :
    formPullback (I := I) (I' := I') f alpha x v =
      alpha (f x) (fun i => mfderiv I I' f x (v i)) := rfl

theorem formPullback_id (alpha : Form I M n) :
    formPullback (I := I) (I' := I) (id : M → M) alpha = alpha := by
  funext x
  ext v
  simp [formPullback, mfderiv_id]

theorem formPullback_comp (f : M → N) (g : N → P)
    (alpha : Form I'' P n)
    (hf : MDifferentiable I I' f) (hg : MDifferentiable I' I'' g) :
    formPullback (I := I) (I' := I'') (g ∘ f) alpha =
      formPullback (I := I) (I' := I') f
        (formPullback (I := I') (I' := I'') g alpha) := by
  funext x
  ext v
  simp only [formPullback, Function.comp_apply]
  rw [mfderiv_comp x (hg (f x)) (hf x)]
  rfl

/-- The local expression of a genuine manifold form in a manifold chart.
The inverse chart's derivative within the model range acts on every tangent
argument, so this also has the correct meaning at corners. -/
noncomputable def inChart (p : M) (alpha : Form I M n) :
    Form 𝓘(ℝ, E) E n :=
  fun y => (alpha ((extChartAt I p).symm y)).compContinuousLinearMap
    (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (Set.range I) y)

/-- The chart pullback viewed through the model-space tangent synonym. -/
noncomputable def inChartModel (p : M) (alpha : Form I M n) :
    E → E [⋀^Fin n]→L[ℝ] ℝ := by
  intro y
  simpa only [TangentSpace] using inChart p alpha y

theorem inChartModel_apply (p : M) (alpha : Form I M n)
    (y : E) (v : Fin n → E) :
    inChartModel p alpha y v =
      alpha ((extChartAt I p).symm y)
        (fun i => mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm
          (Set.range I) y (v i)) := by
  rfl

@[simp] theorem inChartModel_zero (p : M) :
    inChartModel p (0 : Form I M n) = 0 := by
  ext y v
  change (0 : ℝ) = 0
  rfl

theorem inChartModel_add (p : M) (alpha beta : Form I M n) :
    inChartModel p (alpha + beta) =
      inChartModel p alpha + inChartModel p beta := by
  ext y v
  simp [inChartModel_apply]

theorem inChartModel_smul (p : M) (c : ℝ) (alpha : Form I M n) :
    inChartModel p (c • alpha) = c • inChartModel p alpha := by
  ext y v
  simp [inChartModel_apply]

/-- Chartwise smoothness of a tangent-fiber form on the actual chart targets. -/
def ChartSmooth (alpha : Form I M n) : Prop :=
  ∀ p : M, ContDiffOn ℝ ∞ (inChartModel p alpha)
    (extChartAt I p).target

/-- Smooth tangent-fiber forms form a vector subspace. -/
noncomputable def smoothForms : Submodule ℝ (Form I M n) where
  carrier := {alpha | ChartSmooth alpha}
  zero_mem' := by
    intro p
    simpa only [inChartModel_zero] using
      (contDiffOn_const : ContDiffOn ℝ ∞
        (fun _ : E => (0 : E [⋀^Fin n]→L[ℝ] ℝ))
        (extChartAt I p).target)
  add_mem' := by
    intro alpha beta ha hb p
    rw [inChartModel_add]
    exact (ha p).add (hb p)
  smul_mem' := by
    intro c alpha ha p
    rw [inChartModel_smul]
    exact (ha p).const_smul c

section Boundaryless

variable {M₀ : Type*} [TopologicalSpace M₀] [ChartedSpace E M₀]
  [IsManifold 𝓘(ℝ, E) ∞ M₀]

omit [IsManifold 𝓘(ℝ, E) ∞ M₀] in
theorem inChartModel_self_apply (p : M₀)
    (alpha : Form 𝓘(ℝ, E) M₀ n) (y : E) (v : Fin n → E) :
    inChartModel p alpha y v =
      alpha ((extChartAt 𝓘(ℝ, E) p).symm y)
        (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
          (extChartAt 𝓘(ℝ, E) p).symm y (v i)) := by
  simpa [mfderivWithin_univ] using inChartModel_apply p alpha y v

/-- On overlapping charts, the two expressions of a genuine tangent form
are related by pullback under the actual smooth coordinate change. -/
theorem inChartModel_change (alpha : Form 𝓘(ℝ, E) M₀ n)
    (p q : M₀) (y : E)
    (hp : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (hq : (extChartAt 𝓘(ℝ, E) p).symm y ∈
      (extChartAt 𝓘(ℝ, E) q).source) :
    inChartModel p alpha y =
      ContinuousAlternatingMap.compContinuousLinearMap
        (inChartModel q alpha
          ((extChartAt 𝓘(ℝ, E) q) ((extChartAt 𝓘(ℝ, E) p).symm y)))
        (fderiv ℝ
          ((extChartAt 𝓘(ℝ, E) q) ∘
            (extChartAt 𝓘(ℝ, E) p).symm) y) := by
  let Cp := extChartAt 𝓘(ℝ, E) p
  let Cq := extChartAt 𝓘(ℝ, E) q
  let x := Cp.symm y
  let φ : E → E := Cq ∘ Cp.symm
  have hcp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) Cp.symm y := by
    simpa [Cp] using mdifferentiableWithinAt_extChartAt_symm hp
  have hcq : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) Cq x := by
    apply mdifferentiableAt_extChartAt
    simpa [Cq, x, extChartAt_source] using hq
  have hφ : fderiv ℝ φ y =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Cq x).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Cp.symm y) := by
    simpa [φ, x, mfderiv_eq_fderiv] using
      (mfderiv_comp y hcq hcp)
  have hback :
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Cq.symm (φ y)).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Cq x) =
          ContinuousLinearMap.id ℝ E := by
    simpa [Cq, φ, x, mfderivWithin_univ] using
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
        (I := 𝓘(ℝ, E)) hq)
  ext v
  rw [inChartModel_self_apply]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [inChartModel_self_apply]
  have hvalue : Cq.symm (φ y) = x := Cq.left_inv hq
  change alpha x (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Cp.symm y (v i)) =
      alpha (Cq.symm (φ y))
        (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Cq.symm (φ y)
          ((fderiv ℝ φ y) (v i)))
  rw [hvalue, hφ]
  congr 1
  funext i
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    using congrArg (fun L : E →L[ℝ] E =>
      L ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Cp.symm y) (v i))) hback |>.symm

/-- Exterior derivative transported from the preferred chart at each point.
The overlap theorem below proves independence of the chosen local chart. -/
noncomputable def exteriorDerivative (alpha : Form 𝓘(ℝ, E) M₀ n) :
    Form 𝓘(ℝ, E) M₀ (n + 1) :=
  fun x => (extDeriv (inChartModel x alpha) (extChartAt 𝓘(ℝ, E) x x))
    |>.compContinuousLinearMap
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x) x)

/-- At the preferred chart center, the transported derivative recovers the
ordinary exterior derivative of the chart expression. -/
theorem inChartModel_exteriorDerivative_at_center
    (alpha : Form 𝓘(ℝ, E) M₀ n) (p : M₀) :
    inChartModel p (exteriorDerivative alpha)
        (extChartAt 𝓘(ℝ, E) p p) =
      extDeriv (inChartModel p alpha) (extChartAt 𝓘(ℝ, E) p p) := by
  let C := extChartAt 𝓘(ℝ, E) p
  have hsource : p ∈ C.source := mem_extChartAt_source p
  have hcomp :
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C p) ∘L
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C.symm (C p)) =
          ContinuousLinearMap.id ℝ E := by
    simpa [C, mfderivWithin_univ] using
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
        (I := 𝓘(ℝ, E)) hsource)
  ext v
  rw [inChartModel_self_apply]
  simp only [C] at hsource hcomp
  rw [C.left_inv hsource]
  change (extDeriv (inChartModel p alpha) (C p))
      (fun i => (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C p)
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C.symm (C p)) (v i))) = _
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    using congrArg (fun L : E →L[ℝ] E =>
      (extDeriv (inChartModel p alpha) (C p)) (fun i => L (v i))) hcomp

/-- Local coordinate naturality of the actual exterior derivative. This is
the overlap-gluing rule once the two chart expressions have been identified
as tangent-form pullbacks. -/
theorem local_extDeriv_naturality
    {u : Set E} (hu : IsOpen u) {x : E} (hx : x ∈ u)
    (a b : E → E [⋀^Fin n]→L[ℝ] ℝ) (φ : E → E)
    (hab : Set.EqOn a
      (fun y => (b (φ y)).compContinuousLinearMap (fderiv ℝ φ y)) u)
    (hb : DifferentiableAt ℝ b (φ x))
    (hφ : ContDiffAt ℝ 2 φ x) :
    extDeriv a x =
      (extDeriv b (φ x)).compContinuousLinearMap (fderiv ℝ φ x) := by
  have hevent : a =ᶠ[𝓝 x]
      (fun y => (b (φ y)).compContinuousLinearMap (fderiv ℝ φ y)) :=
    by filter_upwards [hu.mem_nhds hx] with y hy; exact hab hy
  rw [hevent.extDeriv_eq]
  exact extDeriv_pullback hb hφ (by norm_num)

/-- Exterior derivatives of a smooth manifold form agree across genuine
chart overlaps. This uses the coordinate change supplied by the manifold
atlas and the normed-space pullback naturality theorem. -/
theorem inChartModel_extDeriv_change
    (alpha : Form 𝓘(ℝ, E) M₀ n) (h : ChartSmooth alpha)
    (p q : M₀) (y : E)
    (hp : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (hq : (extChartAt 𝓘(ℝ, E) p).symm y ∈
      (extChartAt 𝓘(ℝ, E) q).source) :
    extDeriv (inChartModel p alpha) y =
      ContinuousAlternatingMap.compContinuousLinearMap
        (extDeriv (inChartModel q alpha)
          ((extChartAt 𝓘(ℝ, E) q)
            ((extChartAt 𝓘(ℝ, E) p).symm y)))
        (fderiv ℝ
          ((extChartAt 𝓘(ℝ, E) q) ∘
            (extChartAt 𝓘(ℝ, E) p).symm) y) := by
  let Cp := extChartAt 𝓘(ℝ, E) p
  let Cq := extChartAt 𝓘(ℝ, E) q
  let φ : E → E := Cq ∘ Cp.symm
  have hmem : y ∈ (Cp.symm ≫ Cq).source := by
    change y ∈ Cp.target ∩ Cp.symm ⁻¹' Cq.source
    exact ⟨hp, hq⟩
  have hφ : ContDiffAt ℝ 2 φ y := by
    simpa [φ, Cp, Cq] using
      (contDiffWithinAt_ext_coord_change (I := 𝓘(ℝ, E)) q p hmem)
  have hqtarget : φ y ∈ Cq.target := Cq.map_source hq
  have hbc : ContDiffAt ℝ ∞ (inChartModel q alpha) (φ y) :=
    (h q).contDiffAt ((isOpen_extChartAt_target q).mem_nhds hqtarget)
  have hb : DifferentiableAt ℝ (inChartModel q alpha) (φ y) :=
    hbc.differentiableAt (by norm_num)
  have hoverlap : Cp.target ∩ Cp.symm ⁻¹' Cq.source ∈ 𝓝 y :=
    Filter.inter_mem ((isOpen_extChartAt_target p).mem_nhds hp)
      ((continuousAt_extChartAt_symm'' hp).preimage_mem_nhds
        ((isOpen_extChartAt_source q).mem_nhds hq))
  have hevent : inChartModel p alpha =ᶠ[𝓝 y]
      (fun z => (inChartModel q alpha (φ z)).compContinuousLinearMap
        (fderiv ℝ φ z)) := by
    filter_upwards [hoverlap] with z hz
    exact inChartModel_change alpha p q z hz.1 hz.2
  rw [hevent.extDeriv_eq]
  exact extDeriv_pullback hb hφ (by norm_num)

/-- The global tangent-fiber derivative has the expected expression in
*every* chart, not just at the preferred chart center. -/
theorem inChartModel_exteriorDerivative
    (alpha : Form 𝓘(ℝ, E) M₀ n) (h : ChartSmooth alpha)
    (p : M₀) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    inChartModel p (exteriorDerivative alpha) y =
      extDeriv (inChartModel p alpha) y := by
  let x : M₀ := (extChartAt 𝓘(ℝ, E) p).symm y
  have hx : x ∈ (extChartAt 𝓘(ℝ, E) x).source :=
    mem_extChartAt_source x
  have hc := inChartModel_change (exteriorDerivative alpha) p x y hy hx
  have hd := inChartModel_extDeriv_change alpha h p x y hy hx
  have hcenter := inChartModel_exteriorDerivative_at_center alpha x
  rw [hcenter] at hc
  exact hc.trans hd.symm

/-- Smooth manifold forms remain smooth after exterior differentiation. -/
theorem chartSmooth_exteriorDerivative
    (alpha : Form 𝓘(ℝ, E) M₀ n) (h : ChartSmooth alpha) :
    ChartSmooth (exteriorDerivative alpha) := by
  intro p
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ (inChartModel p alpha))
      (extChartAt 𝓘(ℝ, E) p).target :=
    (h p).fderiv_of_isOpen (isOpen_extChartAt_target p) (by simp)
  have hlocal : ContDiffOn ℝ ∞
      (extDeriv (inChartModel p alpha))
      (extChartAt 𝓘(ℝ, E) p).target := by
    simpa only [Function.comp_def, ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
      extDeriv] using
      (ContDiffOn.continuousLinearMap_comp
        (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ) hfd)
  exact hlocal.congr (fun y hy =>
    (inChartModel_exteriorDerivative alpha h p hy))

omit [IsManifold 𝓘(ℝ, E) ∞ M₀] in
/-- The local expression of a chart-smooth manifold form has square-zero
exterior derivative on its actual chart target. -/
theorem inChartModel_extDeriv_extDeriv_zero
    (alpha : Form 𝓘(ℝ, E) M₀ n)
    (h : ChartSmooth alpha) (p : M₀) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    extDeriv (extDeriv (inChartModel p alpha)) y = 0 := by
  have hc : ContDiffAt ℝ ∞ (inChartModel p alpha) y :=
    (h p).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hy)
  exact extDeriv_extDeriv_apply hc (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out)

/-- Square-zero of the exterior derivative on smooth forms over a genuine
boundaryless manifold. The proof uses chart overlap naturality to identify
the first global derivative with the local derivative near each point. -/
theorem exteriorDerivative_exteriorDerivative
    (alpha : Form 𝓘(ℝ, E) M₀ n) (h : ChartSmooth alpha) :
    exteriorDerivative (exteriorDerivative alpha) = 0 := by
  funext x
  let C := extChartAt 𝓘(ℝ, E) x
  let y := C x
  have hy : y ∈ C.target := mem_extChartAt_target x
  have hevent : inChartModel x (exteriorDerivative alpha) =ᶠ[𝓝 y]
      extDeriv (inChartModel x alpha) := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hy] with z hz
    exact inChartModel_exteriorDerivative alpha h x hz
  have hderiv := hevent.extDeriv_eq
  have hzero := inChartModel_extDeriv_extDeriv_zero alpha h x hy
  change ContinuousAlternatingMap.compContinuousLinearMap
      (extDeriv (inChartModel x (exteriorDerivative alpha)) y)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C x) = 0
  rw [hderiv, hzero]
  ext v
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M₀] in
theorem exteriorDerivative_add
    (alpha beta : Form 𝓘(ℝ, E) M₀ n)
    (ha : ChartSmooth alpha) (hb : ChartSmooth beta) :
    exteriorDerivative (alpha + beta) =
      exteriorDerivative alpha + exteriorDerivative beta := by
  funext x
  let y := extChartAt 𝓘(ℝ, E) x x
  have hy : y ∈ (extChartAt 𝓘(ℝ, E) x).target :=
    mem_extChartAt_target x
  have hda : DifferentiableAt ℝ (inChartModel x alpha) y :=
    ((ha x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds hy)).differentiableAt
      (by norm_num)
  have hdb : DifferentiableAt ℝ (inChartModel x beta) y :=
    ((hb x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds hy)).differentiableAt
      (by norm_num)
  change (extDeriv (inChartModel x (alpha + beta)) y).compContinuousLinearMap _ =
    (extDeriv (inChartModel x alpha) y).compContinuousLinearMap _ +
      (extDeriv (inChartModel x beta) y).compContinuousLinearMap _
  rw [inChartModel_add, extDeriv_add hda hdb]
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M₀] in
theorem exteriorDerivative_smul
    (c : ℝ) (alpha : Form 𝓘(ℝ, E) M₀ n) :
    exteriorDerivative (c • alpha) = c • exteriorDerivative alpha := by
  funext x
  change (extDeriv (inChartModel x (c • alpha)) _).compContinuousLinearMap _ =
    c • (extDeriv (inChartModel x alpha) _).compContinuousLinearMap _
  rw [inChartModel_smul, extDeriv_smul]
  rfl

/-- The exterior derivative as a linear map on smooth tangent-fiber forms. -/
noncomputable def smoothExteriorDerivative (k : ℕ) :
    (smoothForms (I := 𝓘(ℝ, E)) (M := M₀) (n := k)) →ₗ[ℝ]
      (smoothForms (I := 𝓘(ℝ, E)) (M := M₀) (n := k + 1)) where
  toFun alpha :=
    ⟨exteriorDerivative alpha.1,
      chartSmooth_exteriorDerivative alpha.1 alpha.2⟩
  map_add' alpha beta := by
    apply Subtype.ext
    exact exteriorDerivative_add alpha.1 beta.1 alpha.2 beta.2
  map_smul' c alpha := by
    apply Subtype.ext
    exact exteriorDerivative_smul c alpha.1

theorem smoothExteriorDerivative_comp_zero (k : ℕ) :
    (smoothExteriorDerivative (E := E) (M₀ := M₀) (k + 1)).comp
      (smoothExteriorDerivative (E := E) (M₀ := M₀) k) = 0 := by
  apply LinearMap.ext
  intro alpha
  apply Subtype.ext
  exact exteriorDerivative_exteriorDerivative alpha.1 alpha.2

/-- Smooth closed forms in degree `k`. -/
noncomputable def closedForms (k : ℕ) :
    Submodule ℝ (smoothForms (I := 𝓘(ℝ, E)) (M := M₀) (n := k)) :=
  (smoothExteriorDerivative (E := E) (M₀ := M₀) k).ker

/-- Exact smooth forms in degree `k+1`. -/
noncomputable def exactForms (k : ℕ) :
    Submodule ℝ (smoothForms (I := 𝓘(ℝ, E)) (M := M₀) (n := k + 1)) :=
  (smoothExteriorDerivative (E := E) (M₀ := M₀) k).range

theorem exactForms_le_closedForms (k : ℕ) :
    exactForms (E := E) (M₀ := M₀) k ≤
      closedForms (E := E) (M₀ := M₀) (k + 1) := by
  intro beta hbeta
  rcases hbeta with ⟨alpha, rfl⟩
  change smoothExteriorDerivative (E := E) (M₀ := M₀) (k + 1)
      (smoothExteriorDerivative (E := E) (M₀ := M₀) k alpha) = 0
  have h := LinearMap.congr_fun
    (smoothExteriorDerivative_comp_zero (E := E) (M₀ := M₀) k) alpha
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h

/-- Exact forms inside the additive group of closed smooth forms. -/
noncomputable def exactClosedAddSubgroup (k : ℕ) :
    AddSubgroup (closedForms (E := E) (M₀ := M₀) (k + 1)) where
  carrier := {alpha | (alpha.1 :
    smoothForms (I := 𝓘(ℝ, E)) (M := M₀) (n := k + 1)) ∈
      exactForms (E := E) (M₀ := M₀) k}
  zero_mem' := by
    exact (exactForms (E := E) (M₀ := M₀) k).zero_mem
  add_mem' := by
    intro a b ha hb
    exact (exactForms (E := E) (M₀ := M₀) k).add_mem ha hb
  neg_mem' := by
    intro a ha
    exact (exactForms (E := E) (M₀ := M₀) k).neg_mem ha

/-- The de Rham cohomology group of closed modulo exact smooth tangent
forms in positive degree `k+1`. No singular-cohomology comparison is used. -/
abbrev positiveDegreeCohomology (k : ℕ) : Type _ :=
  (↥(closedForms (E := E) (M₀ := M₀) (k + 1))) ⧸
    exactClosedAddSubgroup (E := E) (M₀ := M₀) k

end Boundaryless

end QuaternionicSymmetry.ManifoldDifferentialForms
