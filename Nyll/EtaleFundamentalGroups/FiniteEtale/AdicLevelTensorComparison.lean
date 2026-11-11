/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelPullbackModules
public import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
public import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentPullback
public import Nyll.SchemeTheory.Modules.Sections.IhomSections
public import Nyll.SchemeTheory.Modules.Sections.InverseLimit
public import Nyll.SchemeTheory.Modules.Tensor.AffineProjectionFormula
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
public import Nyll.SchemeTheory.Modules.Tensor.PullbackTensorObjIsoHomAppPullbackLocalSection
public import Nyll.SchemeTheory.Modules.Tensor.QuasicoherentTensor
public import Nyll.SchemeTheory.Modules.Tensor.TensorSectionNaturality
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# The actual tensor comparison for closed adic levels

The affine projection formula and the actual pullback tensor comparison
identify a level quotient tensored with a quasicoherent coefficient sheaf
with the level quotient of their tensor product. On original tensor
sections the comparison preserves the pullback unit. Cancellation of that
unit then proves compatibility with the original adic transitions.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (P N : X.Modules) [P.IsQuasicoherent] [N.IsQuasicoherent]

/-- The original projection formula and pullback tensor comparison
identify the actual two level-quotient tensor constructions. -/
def levelPullbackTensorIso (k : ℕ) :
    levelPullbackModule f I P k ⊗ N ≅ levelPullbackModule f I (P ⊗ N) k := by
  let i : level f I k ⟶ X := Limits.pullback.fst f (baseInclusion I k)
  have : IsClosedImmersion i := levelProjection_isClosedImmersion f I k
  have : ((Scheme.Modules.pullback i).obj P).IsQuasicoherent :=
    isQuasicoherent_pullback i P
  exact affineProjectionFormulaIso i ((Scheme.Modules.pullback i).obj P) N ≪≫
    (pushforward i).mapIso (pullbackTensorObjIso i P N).symm

/-- The comparison preserves the original adjunction quotient unit,
not merely the two quotient objects. -/
theorem levelPullbackUnit_tensor_comparison (k : ℕ) :
    (levelPullbackUnit f I P k ▷ N) ≫ (levelPullbackTensorIso f I P N k).hom =
      levelPullbackUnit f I (P ⊗ N) k := by
  let i : level f I k ⟶ X := Limits.pullback.fst f (baseInclusion I k)
  have : IsClosedImmersion i := levelProjection_isClosedImmersion f I k
  have : ((Scheme.Modules.pullback i).obj P).IsQuasicoherent :=
    isQuasicoherent_pullback i P
  let κ : (Scheme.Modules.pullback i).obj (P ⊗ N) ≅
      (Scheme.Modules.pullback i).obj P ⊗ (Scheme.Modules.pullback i).obj N :=
    pullbackTensorObjIso i P N
  apply tensor_hom_ext
  intro U x y
  change κ.inv.app (i ⁻¹ᵁ U)
      ((affineProjectionFormulaIso i ((Scheme.Modules.pullback i).obj P) N).hom.app U
        ((levelPullbackUnit f I P k ▷ N).app U (tensorSections x y))) =
    pullbackLocalSection i (tensorSections x y)
  rw [whiskerRight_app_tensorSections]
  let x' : Γ((Scheme.Modules.pullback i).obj P, i ⁻¹ᵁ U) :=
    pullbackLocalSection i x
  change κ.inv.app (i ⁻¹ᵁ U)
      ((affineProjectionFormulaIso i ((Scheme.Modules.pullback i).obj P) N).hom.app U
        (tensorSections
          (show Γ((pushforward i).obj ((Scheme.Modules.pullback i).obj P), U) from x') y)) =
    pullbackLocalSection i (tensorSections x y)
  have hπ := affineProjectionFormulaIso_hom_tensorSections i
    ((Scheme.Modules.pullback i).obj P) N U
    (show Γ((pushforward i).obj ((Scheme.Modules.pullback i).obj P), U) from x') y
  have hκ := pullbackTensorObjIso_hom_app_pullbackLocalSection i x y
  have h := congrArg (fun z => κ.inv.app (i ⁻¹ᵁ U) z) hκ
  exact (congrArg (fun z => κ.inv.app (i ⁻¹ᵁ U) z) hπ).trans
    (h.symm.trans
      (Iso.hom_inv_id_apply ((moduleSectionsFunctor (i ⁻¹ᵁ U)).mapIso κ)
        (pullbackLocalSection i (tensorSections x y))))

/-- The tensor comparison commutes with every actual quotient
transition, as follows by cancellation of the original epimorphic unit. -/
theorem levelPullbackTensorIso_transition (k : ℕ) :
    (levelPullbackTensorIso f I P N (k + 1)).hom ≫
        levelPullbackTransition f I (P ⊗ N) k =
      (levelPullbackTransition f I P k ▷ N) ≫
        (levelPullbackTensorIso f I P N k).hom := by
  have : Epi (levelPullbackUnit f I P (k + 1) ▷ N) :=
    Functor.map_epi (tensorRight N) (levelPullbackUnit f I P (k + 1))
  apply (cancel_epi (levelPullbackUnit f I P (k + 1) ▷ N)).mp
  calc
    (levelPullbackUnit f I P (k + 1) ▷ N) ≫
        ((levelPullbackTensorIso f I P N (k + 1)).hom ≫
          levelPullbackTransition f I (P ⊗ N) k) =
      levelPullbackUnit f I (P ⊗ N) (k + 1) ≫
        levelPullbackTransition f I (P ⊗ N) k := by
      rw [← Category.assoc, levelPullbackUnit_tensor_comparison]
    _ = levelPullbackUnit f I (P ⊗ N) k :=
      levelPullbackUnit_transition f I (P ⊗ N) k
    _ = (levelPullbackUnit f I P k ▷ N) ≫
        (levelPullbackTensorIso f I P N k).hom :=
      (levelPullbackUnit_tensor_comparison f I P N k).symm
    _ = ((levelPullbackUnit f I P (k + 1) ≫ levelPullbackTransition f I P k) ▷ N) ≫
        (levelPullbackTensorIso f I P N k).hom := by
      rw [levelPullbackUnit_transition]
    _ = (levelPullbackUnit f I P (k + 1) ▷ N) ≫
        ((levelPullbackTransition f I P k ▷ N) ≫
          (levelPullbackTensorIso f I P N k).hom) := by
      rw [comp_whiskerRight, Category.assoc]

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
