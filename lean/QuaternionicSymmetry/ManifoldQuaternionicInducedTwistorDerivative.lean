import QuaternionicSymmetry.ManifoldQuaternionicInducedFiberDerivative
import QuaternionicSymmetry.ManifoldTwistorVerticalLine

/-! Differential of the actual induced twistor map: its base component is
exactly the derivative of the ambient inclusion. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorDerivative
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedCoefficientMap
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedTwistorSmooth
open ManifoldQuaternionicInducedFiberDerivative
open ManifoldQuaternionicInducedSphereChartIdentity
open ManifoldQuaternionicSphereChartSmooth
open ManifoldTwistorSphereCore
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorVerticalComplex
open ManifoldTwistorGlobalAlmostComplex
open Filter
open scoped Manifold ContDiff
noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (R : PositiveQuaternionicKahlerGeometry (E := F) (M := N))
  (ι : N → M)
  (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
  (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
  (hR : IsInducedQuaternionicGeometry P R ι)

private abbrev JF := 𝓘(ℝ,F).prod (𝓡 2)
private abbrev JE := 𝓘(ℝ,E).prod (𝓡 2)

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩
local instance (x : N) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore R.tangent).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2)) geometricSphere
  infer_instance

theorem localSphereMap_fixedFiber (x : N) (u : geometricSphere) :
    ManifoldQuaternionicInducedLocalSphereSmooth.localSphereMap
      P R ι hι hR x (x,u) = geometricFiberMap P R ι hι hR x u := by
  have h := localSphereMap_eq_lift_chart P R ι hι hR x
    (⟨x,u⟩ : SphereBundleTotal R.tangent)
    (mem_chart_source F x) (mem_chart_source E (ι x))
  have hs : ((sphereCore R.tangent).localTriv (achart F x)
      (⟨x,u⟩ : SphereBundleTotal R.tangent)) = (x,u) := by
    apply Prod.ext
    · rfl
    · rw [(sphereCore R.tangent).localTriv_apply]
      exact euclideanSphereCoordChange_self R.tangent (achart F x) x
        (mem_chart_source F x) u
  rw [hs] at h
  have ht : ((sphereCore P.tangent).localTriv (achart E (ι x))
      (sphereTotalMap P R ι hι hR (⟨x,u⟩ : SphereBundleTotal R.tangent))).2 =
      (sphereTotalMap P R ι hι hR (⟨x,u⟩ : SphereBundleTotal R.tangent)).2 := by
    rw [(sphereCore P.tangent).localTriv_apply]
    exact euclideanSphereCoordChange_self P.tangent (achart E (ι x)) (ι x)
      (mem_chart_source E (ι x)) _
  rw [ht] at h
  exact h

include hSmooth in
theorem localProductMap_vertical_mfderiv
    (x : N) (u : geometricSphere) (v : TangentSpace (𝓡 2) u) :
    mfderiv (JF (F := F)) (JE (E := E))
      (localProductMap P R ι hι hR x) (x,u) (0,v) =
      (0, mfderiv (𝓡 2) (𝓡 2)
        (geometricFiberMap P R ι hι hR x) u v) := by
  let S : geometricSphere → N × geometricSphere := fun t => (x,t)
  let L := localProductMap P R ι hι hR x
  let G : geometricSphere → M × geometricSphere :=
    fun t => (ι x, geometricFiberMap P R ι hι hR x t)
  have hfun : L ∘ S = G := by
    funext t
    apply Prod.ext
    · rfl
    · exact localSphereMap_fixedFiber P R ι hι hR x t
  have hS : MDifferentiableAt (𝓡 2) (JF (F := F)) S u :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hL : MDifferentiableAt (JF (F := F)) (JE (E := E)) L (S u) :=
    (localProductMap_smoothAt_center P R ι hSmooth hι hR x u).mdifferentiableAt
      (by simp)
  have hg : MDifferentiableAt (𝓡 2) (𝓡 2)
      (geometricFiberMap P R ι hι hR x) u :=
    (geometricFiberMap_smooth P R ι hι hR x).mdifferentiable (by simp) u
  have hd := congrArg
    (fun H : geometricSphere → M × geometricSphere =>
      mfderiv (𝓡 2) (JE (E := E)) H u v) hfun
  change mfderiv (𝓡 2) (JE (E := E)) (L ∘ S) u v =
    mfderiv (𝓡 2) (JE (E := E)) G u v at hd
  rw [mfderiv_comp u hL hS] at hd
  have hSd : mfderiv (𝓡 2) (JF (F := F)) S u v = (0,v) := by
    rw [show S = (fun t : geometricSphere => (x,t)) from rfl,
      mfderiv_prod_right]
    rfl
  change (mfderiv (JF (F := F)) (JE (E := E)) L (S u))
      ((mfderiv (𝓡 2) (JF (F := F)) S u) v) =
    (mfderiv (𝓡 2) (JE (E := E)) G u) v at hd
  rw [hSd] at hd
  have hGd : mfderiv (𝓡 2) (JE (E := E)) G u v =
      (0, mfderiv (𝓡 2) (𝓡 2)
        (geometricFiberMap P R ι hι hR x) u v) := by
    rw [show G = (fun t : geometricSphere =>
        (ι x, geometricFiberMap P R ι hι hR x t)) from rfl,
      mfderiv_prodMk mdifferentiableAt_const hg, mfderiv_const]
    rfl
  exact hd.trans hGd

include hSmooth in
theorem sphereTotalMap_mfderiv_eq_local
    (z : SphereBundleTotal R.tangent) :
    mfderiv (JF (F := F)) (JE (E := E))
      (sphereTotalMap P R ι hι hR) z =
      mfderiv (JF (F := F)) (JE (E := E))
        (localProductMap P R ι hι hR z.1) (z.1,z.2) := by
  let c := z.1
  let w := sphereTotalMap P R ι hι hR z
  let C := chartAt (N × geometricSphere) z
  let D := chartAt (M × geometricSphere) w
  let L := localProductMap P R ι hι hR c
  have hC : MDifferentiableAt (JF (F := F)) (JF (F := F))
      (C : SphereBundleTotal R.tangent → N × geometricSphere) z :=
    (preferredLocalTriv_smoothAt R.tangent z).mdifferentiableAt (by simp)
  have hD : MDifferentiableAt (JE (E := E)) (JE (E := E))
      (D : SphereBundleTotal P.tangent → M × geometricSphere) w :=
    (preferredLocalTriv_smoothAt P.tangent w).mdifferentiableAt (by simp)
  have hL : MDifferentiableAt (JF (F := F)) (JE (E := E)) L (C z) := by
    change MDifferentiableAt (JF (F := F)) (JE (E := E)) L (c,(C z).2)
    exact (localProductMap_smoothAt_center P R ι hSmooth hι hR c (C z).2)
      |>.mdifferentiableAt (by simp)
  have hΦ : MDifferentiableAt (JF (F := F)) (JE (E := E))
      (sphereTotalMap P R ι hι hR) z :=
    (sphereTotalMap_contMDiff P R ι hSmooth hι hR).mdifferentiable (by simp) z
  have hbase : Continuous (fun y : SphereBundleTotal R.tangent => y.1) :=
    (ManifoldTwistorSphereManifold.sphereProjection_smooth R.tangent).continuous
  have h₁ : ∀ᶠ y in nhds z, y.1 ∈ (chartAt F c).source :=
    (((chartAt F c).open_source).preimage hbase).mem_nhds (mem_chart_source F c)
  have h₂ : ∀ᶠ y in nhds z, ι y.1 ∈ (chartAt E (ι c)).source :=
    (((chartAt E (ι c)).open_source).preimage
      (hSmooth.continuous.comp hbase)).mem_nhds (mem_chart_source E (ι c))
  have heq : (fun y : SphereBundleTotal R.tangent =>
      D (sphereTotalMap P R ι hι hR y)) =ᶠ[nhds z]
      (fun y => L (C y)) := by
    filter_upwards [h₁, h₂] with y hy₁ hy₂
    exact (localProductMap_eq_chart P R ι hι hR c y hy₁ hy₂).symm
  have hd := heq.mfderiv_eq (I := JF (F := F)) (I' := JE (E := E))
  change mfderiv (JF (F := F)) (JE (E := E))
      (D ∘ sphereTotalMap P R ι hι hR) z =
    mfderiv (JF (F := F)) (JE (E := E)) (L ∘ C) z at hd
  rw [mfderiv_comp z hD hΦ, mfderiv_comp z hL hC] at hd
  have hdC : mfderiv (JF (F := F)) (JF (F := F))
      (C : SphereBundleTotal R.tangent → N × geometricSphere) z =
        ContinuousLinearMap.id ℝ _ := preferredTriv_mfderiv R.tangent z
  have hdD : mfderiv (JE (E := E)) (JE (E := E))
      (D : SphereBundleTotal P.tangent → M × geometricSphere) w =
        ContinuousLinearMap.id ℝ _ := preferredTriv_mfderiv P.tangent w
  have hDw : D w = (w.1,w.2) := by
    apply Prod.ext
    · rfl
    · change ((sphereCore P.tangent).localTriv (achart E w.1) w).2 = w.2
      rw [(sphereCore P.tangent).localTriv_apply]
      exact euclideanSphereCoordChange_self P.tangent (achart E w.1) w.1
        (mem_chart_source E w.1) w.2
  rw [hdC, hdD] at hd
  rw [hDw] at hd
  simp only [ContinuousLinearMap.comp_id] at hd
  have hCz : C z = (c,z.2) := by
    apply Prod.ext
    · rfl
    · change ((sphereCore R.tangent).localTriv (achart F c) z).2 = z.2
      rw [(sphereCore R.tangent).localTriv_apply]
      exact euclideanSphereCoordChange_self R.tangent (achart F c) c
        (mem_chart_source F c) z.2
  apply ContinuousLinearMap.ext
  intro v
  have hdv := congrArg
    (fun L' : TangentSpace (JF (F := F)) z →L[ℝ]
        TangentSpace (JE (E := E)) w => L' v) hd
  change (mfderiv (JF (F := F)) (JE (E := E))
      (sphereTotalMap P R ι hι hR) z) v =
    (mfderiv (JF (F := F)) (JE (E := E)) L (C z)) v at hdv
  rw [hCz] at hdv
  exact hdv

theorem sphereTotalMap_fiber (z : SphereBundleTotal R.tangent) :
    (sphereTotalMap P R ι hι hR z).2 =
      geometricFiberMap P R ι hι hR z.1 z.2 := rfl

include hSmooth in
theorem sphereTotalMap_vertical_mfderiv_snd
    (z : SphereBundleTotal R.tangent)
    (v : TangentSpace (𝓡 2) (z.2 : geometricSphere)) :
    (mfderiv (JF (F := F)) (JE (E := E))
      (sphereTotalMap P R ι hι hR) z (0,v)).2 =
        mfderiv (𝓡 2) (𝓡 2)
          (geometricFiberMap P R ι hι hR z.1) z.2 v := by
  rw [sphereTotalMap_mfderiv_eq_local P R ι hSmooth hι hR z]
  exact congrArg Prod.snd
    (localProductMap_vertical_mfderiv P R ι hSmooth hι hR z.1 z.2 v)

include hSmooth in
theorem mfderiv_sphereTotalMap_mem_vertical
    (z : SphereBundleTotal R.tangent)
    (v : TangentSpace (JF (F := F)) z)
    (hv : v ∈ verticalTangentSubmodule R.tangent z) :
    mfderiv (JF (F := F)) (JE (E := E))
      (sphereTotalMap P R ι hι hR) z v ∈
      verticalTangentSubmodule P.tangent (sphereTotalMap P R ι hι hR z) := by
  rw [mem_verticalTangentSubmodule_iff] at hv ⊢
  have hv0 : v.1 = 0 := hv
  have hv' : v = (0,v.2) := Prod.ext hv0 rfl
  change (mfderiv (JF (F := F)) (JE (E := E))
      (sphereTotalMap P R ι hι hR) z v).1 = 0
  rw [hv', sphereTotalMap_mfderiv_eq_local P R ι hSmooth hι hR z]
  exact congrArg Prod.fst
    (localProductMap_vertical_mfderiv P R ι hSmooth hι hR z.1 z.2 v.2)

include hSmooth in
theorem vertical_mfderiv_coefficient
    (z : SphereBundleTotal R.tangent)
    (v : verticalTangentSubmodule R.tangent z) :
    ((verticalTangentEquiv P.tangent (sphereTotalMap P R ι hι hR z))
      ⟨mfderiv (JF (F := F)) (JE (E := E))
        (sphereTotalMap P R ι hι hR) z v.1,
        mfderiv_sphereTotalMap_mem_vertical P R ι hSmooth hι hR z v.1 v.2⟩).1 =
      coefficientMap P R ι hι hR z.1
        ((verticalTangentEquiv R.tangent z v).1) := by
  have hv0 : v.1.1 = 0 :=
    (mem_verticalTangentSubmodule_iff R.tangent z v.1).mp v.2
  have hv : v.1 = (0,v.1.2) := Prod.ext hv0 rfl
  change EuclideanSpace.equiv (Fin 3) ℝ
      (sphereTangentMap (sphereTotalMap P R ι hι hR z).2
        (mfderiv (JF (F := F)) (JE (E := E))
          (sphereTotalMap P R ι hι hR) z v.1).2) =
    coefficientMap P R ι hι hR z.1
      (EuclideanSpace.equiv (Fin 3) ℝ (sphereTangentMap z.2 v.1.2))
  rw [hv]
  rw [sphereTotalMap_vertical_mfderiv_snd P R ι hSmooth hι hR z v.1.2]
  rw [sphereTotalMap_fiber P R ι hι hR z]
  have h := sphereTangentMap_geometricFiberMap P R ι hι hR z.1 z.2 v.1.2
  exact congrArg (EuclideanSpace.equiv (Fin 3) ℝ) h

include hSmooth in
def actualVerticalDerivative (z : SphereBundleTotal R.tangent) :
    verticalTangentSubmodule R.tangent z →ₗ[ℝ]
      verticalTangentSubmodule P.tangent (sphereTotalMap P R ι hι hR z) where
  toFun v := ⟨mfderiv (JF (F := F)) (JE (E := E))
    (sphereTotalMap P R ι hι hR) z v.1,
    mfderiv_sphereTotalMap_mem_vertical P R ι hSmooth hι hR z v.1 v.2⟩
  map_add' u v := by
    apply Subtype.ext
    exact map_add (mfderiv (JF (F := F)) (JE (E := E))
      (sphereTotalMap P R ι hι hR) z) u.1 v.1
  map_smul' c v := by
    apply Subtype.ext
    exact map_smul (mfderiv (JF (F := F)) (JE (E := E))
      (sphereTotalMap P R ι hι hR) z) c v.1

include hSmooth in
theorem actualVerticalDerivative_coefficient
    (z : SphereBundleTotal R.tangent)
    (v : verticalTangentSubmodule R.tangent z) :
    ((verticalTangentEquiv P.tangent (sphereTotalMap P R ι hι hR z))
      (actualVerticalDerivative P R ι hSmooth hι hR z v)).1 =
      coefficientMap P R ι hι hR z.1
        ((verticalTangentEquiv R.tangent z v).1) :=
  vertical_mfderiv_coefficient P R ι hSmooth hι hR z v

include hSmooth in
theorem sphereTotalMap_mfderiv_fst
    (z : SphereBundleTotal R.tangent)
    (v : TangentSpace (JF (F := F)) z) :
    (mfderiv (JF (F := F)) (JE (E := E))
      (sphereTotalMap P R ι hι hR) z v).1 =
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι z.1 v.1 := by
  let πR : SphereBundleTotal R.tangent → N := fun y => y.1
  let πP : SphereBundleTotal P.tangent → M := fun y => y.1
  let Φ := sphereTotalMap P R ι hι hR
  have hπR : MDifferentiableAt (JF (F := F)) 𝓘(ℝ,F) πR z :=
    (ManifoldTwistorSphereManifold.sphereProjection_smooth R.tangent).mdifferentiable
      (by simp) z
  have hπP : MDifferentiableAt (JE (E := E)) 𝓘(ℝ,E) πP (Φ z) :=
    (ManifoldTwistorSphereManifold.sphereProjection_smooth P.tangent).mdifferentiable
      (by simp) (Φ z)
  have hΦ : MDifferentiableAt (JF (F := F)) (JE (E := E)) Φ z :=
    (sphereTotalMap_contMDiff P R ι hSmooth hι hR).mdifferentiable (by simp) z
  have hι' : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) ι z.1 :=
    hSmooth.mdifferentiable (by simp) z.1
  have hfun : πP ∘ Φ = ι ∘ πR := by
    funext y
    exact sphereTotalMap_base P R ι hι hR y
  have hd := congrArg
    (fun f : SphereBundleTotal R.tangent → M =>
      mfderiv (JF (F := F)) 𝓘(ℝ,E) f z v) hfun
  change mfderiv (JF (F := F)) 𝓘(ℝ,E) (πP ∘ Φ) z v =
    mfderiv (JF (F := F)) 𝓘(ℝ,E) (ι ∘ πR) z v at hd
  rw [mfderiv_comp z hπP hΦ] at hd
  dsimp only [πR] at hd
  rw [mfderiv_comp z hι' hπR] at hd
  dsimp only [πP, πR, Φ] at hd
  rw [ManifoldTwistorGlobalAlmostComplex.sphereProjection_mfderiv P.tangent,
    ManifoldTwistorGlobalAlmostComplex.sphereProjection_mfderiv R.tangent] at hd
  exact hd

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorDerivative
