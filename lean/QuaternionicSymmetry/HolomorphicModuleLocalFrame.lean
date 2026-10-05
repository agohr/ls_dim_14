import QuaternionicSymmetry.HolomorphicLineModuleIsoToGauge

/-! Local rank-one trivializations of an arbitrary genuine module sheaf over
holomorphic functions. A frame consists of linear coordinates on every
smaller open, commuting with the actual sheaf restrictions. This is local
freeness as a sheaf, not merely freeness of one module of sections. -/

namespace QuaternionicSymmetry.HolomorphicModuleLocalFrame

open CategoryTheory TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf HolomorphicLineModuleLocalFree
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (M : SheafOfModules.{0} (structureSheaf (B := B) IB))

/-- A rank-one trivialization of the restricted module sheaf on `U`, stated
on all its open subsets with genuine restriction naturality. -/
structure LocalFrame (U : Opens B) where
  coordinate (V : Opens B) (hVU : V ≤ U) :
    M.val.obj (op V) ≃ₗ[Functions IB V] Functions IB V
  restrict (V W : Opens B) (hWV : W ≤ V) (hVU : V ≤ U)
      (s : M.val.obj (op V)) :
    coordinate W (hWV.trans hVU) (M.val.map (homOfLE hWV).op s) =
      ContMDiffMap.restrictRingHom IB 𝓘(ℂ,ℂ) ℂ hWV (coordinate V hVU s)

/-- Local freeness of rank one is the existence of such a sheaf frame near
each point; no global bundle or classification is included in this property. -/
def IsLocallyFreeRankOne : Prop :=
  ∀ x : B, ∃ U : Opens B, x ∈ U ∧ Nonempty (LocalFrame IB M U)

variable {IB M}

def LocalFrame.restrictTo {U V : Opens B} (f : LocalFrame IB M U)
    (hVU : V ≤ U) : LocalFrame IB M V where
  coordinate W hWV := f.coordinate W (hWV.trans hVU)
  restrict W T hTW hWV s := f.restrict W T hTW (hWV.trans hVU) s

/-- Unit frames restrict to the unit frame, not merely a scalar multiple. -/
theorem LocalFrame.unit_restrict {U : Opens B} (f : LocalFrame IB M U)
    (V W : Opens B) (hWV : W ≤ V) (hVU : V ≤ U) :
    M.val.map (homOfLE hWV).op ((f.coordinate V hVU).symm 1) =
      (f.coordinate W (hWV.trans hVU)).symm 1 := by
  apply (f.coordinate W (hWV.trans hVU)).injective
  rw [f.restrict V W hWV hVU, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]
  exact map_one _

/-- Coordinates in two frames differ by multiplication by the coordinates
of the first unit frame in the second frame. -/
theorem LocalFrame.coordinate_change {U V : Opens B}
    (f : LocalFrame IB M U) (g : LocalFrame IB M V)
    (W : Opens B) (hWU : W ≤ U) (hWV : W ≤ V)
    (s : M.val.obj (op W)) :
    g.coordinate W hWV s =
      g.coordinate W hWV ((f.coordinate W hWU).symm 1) *
        f.coordinate W hWU s := by
  have hs : s = (f.coordinate W hWU s) • (f.coordinate W hWU).symm 1 := by
    apply (f.coordinate W hWU).injective
    simp
  calc
    g.coordinate W hWV s = g.coordinate W hWV
        ((f.coordinate W hWU s) • (f.coordinate W hWU).symm 1) :=
      congrArg (g.coordinate W hWV) hs
    _ = _ := by rw [map_smul]; exact mul_comm _ _

variable (IB)

/-- The actual chart section coordinates already constructed for a line
bundle are local sheaf frames in the above sense. -/
def lineCoreFrame {ι : Type*} (Z : VectorBundleCore ℂ B ℂ ι)
    [Z.IsContMDiff IB ∞] (i : ι) :
    LocalFrame IB (moduleSheaf IB Z) ⟨Z.baseSet i, Z.isOpen_baseSet i⟩ where
  coordinate V hV := coordinateLinearEquiv IB Z i V hV
  restrict V W hWV hV s := coordinate_restrict IB Z i V W hWV hV s

theorem moduleSheaf_locallyFreeRankOne {ι : Type*}
    (Z : VectorBundleCore ℂ B ℂ ι) [Z.IsContMDiff IB ∞] :
    IsLocallyFreeRankOne IB (moduleSheaf IB Z) := by
  intro x
  exact ⟨⟨Z.baseSet (Z.indexAt x), Z.isOpen_baseSet (Z.indexAt x)⟩,
    Z.mem_baseSet_at x, ⟨lineCoreFrame IB Z (Z.indexAt x)⟩⟩

end
end QuaternionicSymmetry.HolomorphicModuleLocalFrame
