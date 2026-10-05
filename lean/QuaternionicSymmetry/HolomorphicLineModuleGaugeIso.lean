import QuaternionicSymmetry.HolomorphicLineModuleLocalFree
import QuaternionicSymmetry.HolomorphicLineGaugeToBundleIso

/-! All-overlap holomorphic bundle gauges induce genuine isomorphisms of
sheaves of modules over the holomorphic function sheaf. Consequently the
bundle-to-module-sheaf construction respects actual bundle isomorphism,
including changes of cover. The converse and essential surjectivity onto
invertible sheaves are not asserted here. -/

namespace QuaternionicSymmetry.HolomorphicLineModuleGaugeIso

open CategoryTheory TopologicalSpace Manifold Bundle
open HolomorphicLineModuleSheaf HolomorphicLineGauge
open HolomorphicLineGaugeToBundleIso
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F ι κ : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (Z : VectorBundleCore ℂ B ℂ ι) [Z.IsContMDiff IB ∞]

theorem coefficientPrelocal_iff_total_holomorphic {U : Opens B}
    (s : ∀ x : U, Z.Fiber x) :
    (coefficientPrelocal IB Z).pred s ↔
      ContMDiff IB (IB.prod 𝓘(ℂ,ℂ)) ∞
        (fun x : U => (⟨x.1, s x⟩ : TotalSpace ℂ Z.Fiber)) := by
  letI (i : ι) : MemTrivializationAtlas (Z.localTriv i) := ⟨⟨i, rfl⟩⟩
  constructor
  · intro hs x
    let i := Z.indexAt x.1
    have hx : x.1 ∈ Z.baseSet i := Z.mem_baseSet_at x.1
    have hcoeff := (hs i x hx).contMDiffAt
      (((Z.isOpen_baseSet i).preimage continuous_subtype_val).mem_nhds hx)
    apply ((Z.localTriv i).contMDiffAt_iff
      (f := fun y : U => (⟨y.1, s y⟩ : TotalSpace ℂ Z.Fiber))
      ((Z.mem_localTriv_source i _).2 hx)).2
    exact ⟨contMDiff_subtype_val.contMDiffAt, hcoeff⟩
  · intro hs i x hx
    exact (((Z.localTriv i).contMDiffAt_iff
      (f := fun y : U => (⟨y.1, s y⟩ : TotalSpace ℂ Z.Fiber))
      ((Z.mem_localTriv_source i _).2 hx)).1 (hs x)).2.contMDiffWithinAt

variable (W : VectorBundleCore ℂ B ℂ κ) [W.IsContMDiff IB ∞]

/-- The actual pointwise bundle map on local section modules. Its
linearity is over the full ring of local holomorphic functions. -/
def gaugeSectionMap (e : GaugeIso (IB := IB) Z W) (U : Opens B) :
    sectionSubmodule IB Z U →ₗ[Functions IB U] sectionSubmodule IB W U where
  toFun s := ⟨fun x => gaugeFiberEquiv e x.1 (s.1 x), by
    change (coefficientPrelocal IB W).sheafify.pred
      (fun x : U => gaugeFiberEquiv e x.1 (s.1 x))
    intro x
    obtain ⟨V, hxV, j, hV⟩ := s.property x
    refine ⟨V, hxV, j, ?_⟩
    apply (coefficientPrelocal_iff_total_holomorphic IB W _).2
    exact (gaugeTotalMap_holomorphic e).comp
      ((coefficientPrelocal_iff_total_holomorphic IB Z _).1 hV)⟩
  map_add' s t := by
    apply Subtype.ext
    funext x
    exact (gaugeFiberEquiv e x.1).map_add (s.1 x) (t.1 x)
  map_smul' f s := by
    apply Subtype.ext
    funext x
    exact map_smul (gaugeFiberEquiv e x.1) (f x) (s.1 x)

/-- The local maps commute with actual sheaf restriction. -/
def gaugeSheafHom (e : GaugeIso (IB := IB) Z W) :
    moduleSheaf IB Z ⟶ moduleSheaf IB W where
  val := {
    app := fun U => ModuleCat.ofHom
      (X := (moduleSheaf IB Z).val.obj U)
      (Y := (moduleSheaf IB W).val.obj U)
      (gaugeSectionMap IB Z W e U.unop)
    naturality := by intro U V j; rfl }

/-- Holomorphic bundle gauges give genuine module-sheaf isomorphisms;
the inverse is the backward gauge, not an assumed sheaf equivalence. -/
def gaugeSheafIso (e : GaugeIso (IB := IB) Z W) :
    moduleSheaf IB Z ≅ moduleSheaf IB W where
  hom := gaugeSheafHom IB Z W e
  inv := gaugeSheafHom IB W Z e.symm
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    funext x
    exact (gaugeFiberEquiv e x.1).symm_apply_apply (s.1 x)
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    funext x
    exact (gaugeFiberEquiv e x.1).apply_symm_apply (s.1 x)

end
end QuaternionicSymmetry.HolomorphicLineModuleGaugeIso
