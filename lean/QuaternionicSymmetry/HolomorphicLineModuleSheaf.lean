import QuaternionicSymmetry.HolomorphicLineCoreClasses
import Mathlib.Geometry.Manifold.Sheaf.Smooth
import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-! Actual holomorphic line-core sections as a sheaf of modules over the
actual holomorphic function sheaf. The scalar action is multiplication by
varying holomorphic functions, not just constant complex numbers. Local
freeness and the converse reconstruction from invertible sheaves are
separate steps. Mathlib's function sheaf here requires a base in `Type`. -/

namespace QuaternionicSymmetry.HolomorphicLineModuleSheaf

open CategoryTheory TopologicalSpace Manifold
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F ι : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H) (Z : VectorBundleCore ℂ B ℂ ι)

/-- The actual coefficient of a section in a fixed bundle chart. -/
def coefficient (i : ι) {U : Opens B}
    (s : ∀ x : U, Z.Fiber x) (x : U) : ℂ :=
  Z.coordChange (Z.indexAt x.1) i x.1 (s x)

def coefficientPrelocal :
    TopCat.PrelocalPredicate (fun x : TopCat.of B => Z.Fiber x) where
  pred {U} s := ∀ i : ι,
    ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (coefficient Z i s)
      {x : U | x.1 ∈ Z.baseSet i}
  res {U V} j s hs i := by
    exact (hs i).comp (contMDiff_inclusion j.le).contMDiffOn
      (fun _ hx => hx)

/-- The genuine ring of holomorphic scalar functions on an open set. -/
abbrev Functions (U : Opens B) := C^∞⟮IB, U; 𝓘(ℂ,ℂ), ℂ⟯

/-- Pointwise multiplication by holomorphic scalar functions on arbitrary
raw dependent fiber sections. -/
instance rawSectionModule (U : Opens B) :
    Module (Functions IB U) (∀ x : U, Z.Fiber x) :=
  Module.compHom _ ContMDiffMap.coeFnRingHom

/-- Locally holomorphic line sections are a module over holomorphic
functions, with the actual pointwise scalar action. -/
def sectionSubmodule (U : Opens B) :
    Submodule (Functions IB U) (∀ x : U, Z.Fiber x) where
  carrier := {s | (coefficientPrelocal IB Z).sheafify.pred s}
  zero_mem' := by
    apply TopCat.PrelocalPredicate.sheafifyOf
    intro i
    convert contMDiffOn_const using 1
    funext x
    exact map_zero _
  add_mem' := by
    intro s t hs ht
    let P := coefficientPrelocal IB Z
    apply P.sheafify_inductionOn₂' P P (fun x y => x + y) ?_ hs ht
    intro V W a b ha hb i
    have ha' := P.res (Opens.infLELeft V W) a ha i
    have hb' := P.res (Opens.infLERight V W) b hb i
    convert ha'.add hb' using 1
    funext x
    exact map_add _ _ _
  smul_mem' := by
    intro f s hs x
    obtain ⟨V, hxV, j, hV⟩ := hs x
    refine ⟨V, hxV, j, ?_⟩
    intro i
    have hf : ContMDiff IB 𝓘(ℂ,ℂ) ∞
        (fun y : V => f ⟨y.1, j.le y.2⟩) :=
      f.contMDiff.comp (contMDiff_inclusion j.le)
    convert hf.contMDiffOn.smul (hV i) using 1
    funext y
    exact map_smul (Z.coordChange (Z.indexAt y.1) i y.1)
      (f ⟨y.1, j.le y.2⟩) (s ⟨y.1, j.le y.2⟩)

def sectionSheaf : TopCat.Sheaf (Type _) (TopCat.of B) :=
  TopCat.subsheafToTypes (coefficientPrelocal IB Z).sheafify

instance sectionSheaf_addCommGroup (U : (Opens (TopCat.of B))ᵒᵖ) :
    AddCommGroup ((sectionSheaf IB Z).presheaf.obj U) :=
  inferInstanceAs (AddCommGroup (sectionSubmodule IB Z U.unop))

instance sectionSheaf_module (U : (Opens (TopCat.of B))ᵒᵖ) :
    Module (Functions IB U.unop) ((sectionSheaf IB Z).presheaf.obj U) :=
  inferInstanceAs (Module (Functions IB U.unop) (sectionSubmodule IB Z U.unop))

def restrictionAddHom {U V : (Opens (TopCat.of B))ᵒᵖ} (j : U ⟶ V) :
    (sectionSheaf IB Z).presheaf.obj U →+
      (sectionSheaf IB Z).presheaf.obj V where
  toFun := (sectionSheaf IB Z).presheaf.map j
  map_zero' := rfl
  map_add' _ _ := rfl

def sectionPresheafAdd : TopCat.Presheaf AddCommGrpCat (TopCat.of B) where
  obj U := AddCommGrpCat.of ((sectionSheaf IB Z).presheaf.obj U)
  map j := AddCommGrpCat.ofHom (restrictionAddHom IB Z j)
  map_id _ := rfl
  map_comp _ _ := rfl

theorem sectionPresheafAdd_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology (TopCat.of B))
      (sectionPresheafAdd IB Z) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat)]
  exact (sectionSheaf IB Z).cond

/-- The actual holomorphic function sheaf, as a sheaf of rings. -/
abbrev structureSheaf : TopCat.Sheaf RingCat (TopCat.of B) :=
  smoothSheafRing IB 𝓘(ℂ,ℂ) B ℂ

/-- Restrictions are semilinear over restriction of holomorphic scalar
functions, so the sections form a genuine presheaf of modules. -/
def sectionPresheafModule : PresheafOfModules (structureSheaf (B := B) IB).val := by
  letI (U : (Opens (TopCat.of B))ᵒᵖ) :
      Module ((structureSheaf (B := B) IB).val.obj U)
        ((sectionPresheafAdd IB Z).obj U) := sectionSheaf_module IB Z U
  exact PresheafOfModules.ofPresheaf (sectionPresheafAdd IB Z)
    (by intro U V j f s; rfl)

/-- The line-section object in Mathlib's actual category of modules over
the holomorphic structure sheaf. -/
def moduleSheaf : SheafOfModules (structureSheaf (B := B) IB) where
  val := sectionPresheafModule IB Z
  isSheaf := sectionPresheafAdd_isSheaf IB Z

end
end QuaternionicSymmetry.HolomorphicLineModuleSheaf
