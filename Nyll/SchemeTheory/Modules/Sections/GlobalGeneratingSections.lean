/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.AffineOpenModuleEpi
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
import Nyll.SchemeTheory.Modules.Sections.SectionsGluing
import Nyll.SchemeTheory.Modules.Submodules.FiniteSectionSubmodule
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Actual generating sections detected on affine opens

Global sections determine their native morphism from the free sheaf.
If their restrictions span the section modules on an affine cover, that
morphism is epimorphic on every member of the cover. Cancellation and
sheaf separatedness then prove that the original morphism is epimorphic.
This constructs native generating sections with the given index family.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private theorem epi_of_epi_over_cover {X : Scheme.{u}}
    {M N : SheafOfModules.{u} X.ringCatSheaf} (φ : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hφ : ∀ i, Epi (φ.over (U i))) : Epi φ := by
  constructor
  intro P ψ χ h
  have hlocal : ∀ i, ψ.over (U i) = χ.over (U i) := by
    intro i
    have : Epi (φ.over (U i)) := hφ i
    apply (cancel_epi (φ.over (U i))).mp
    exact (SheafOfModules.overFunctor X.ringCatSheaf (U i)).congr_map h
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  let P' : X.Modules := P
  have hcover : W.unop ≤ ⨆ i, W.unop ⊓ U i := by
    intro x hx
    have hxU : x ∈ ⨆ i, U i := by
      rw [hU]
      exact Set.mem_univ x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxU
    exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  apply (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible P'
    (fun i => W.unop ⊓ U i) W.unop (fun _ => inf_le_left) hcover).1
  intro i
  let Z : Over (U i) :=
    Over.mk (homOfLE (inf_le_right : W.unop ⊓ U i ≤ U i))
  have hi := congrArg
    (fun f : N.over (U i) ⟶ P.over (U i) =>
      (f.val.app (op Z)).hom
        (N.val.map (homOfLE (inf_le_left : W.unop ⊓ U i ≤ W.unop)).op m))
    (hlocal i)
  exact (PresheafOfModules.naturality_apply ψ.val (homOfLE inf_le_left).op m).symm.trans
    (hi.trans (PresheafOfModules.naturality_apply χ.val (homOfLE inf_le_left).op m))

variable {X : Scheme.{u}} (M : X.Modules)
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]

/-- Global sections spanning the actual modules of sections on an affine
cover define native generating sections. The map from the free sheaf is
the original `freeHomEquiv` map of these sections. -/
def generatingSectionsOfAffineSpans {I ι : Type u} (s : I → Γ(M, ⊤))
    (U : ι → X.Opens) (hAffine : ∀ i, IsAffineOpen (U i)) (hU : ⨆ i, U i = ⊤)
    (hspan : ∀ i, Submodule.span Γ(X, U i)
      (Set.range (fun a : I =>
        M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s a))) = ⊤) :
    M.GeneratingSections where
  I := I
  s := fun a => M.topSection (s a)
  epi := by
    let P : SheafOfModules.{u} X.ringCatSheaf :=
      SheafOfModules.free (R := X.ringCatSheaf) I
    let φ : P ⟶ (show SheafOfModules.{u} X.ringCatSheaf from M) :=
      M.freeHomEquiv.symm (fun a => M.topSection (s a))
    apply epi_of_epi_over_cover φ U hU
    intro i
    let l : Γ((show X.Modules from P), U i) →ₗ[Γ(X, U i)] Γ(M, U i) :=
      (φ.val.app (op (U i))).hom
    have hrange : Submodule.span Γ(X, U i)
        (Set.range (fun a : I =>
          M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s a))) ≤ l.range := by
      apply Submodule.span_le.mpr
      rintro y ⟨a, rfl⟩
      refine ⟨(SheafOfModules.freeSection (R := X.ringCatSheaf) a).val (op (U i)), ?_⟩
      exact congrArg (fun t : M.sections => t.val (op (U i)))
        (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
          (fun b => M.topSection (s b)) a)
    have hl : Function.Surjective l := by
      apply LinearMap.range_eq_top.mp
      rw [hspan i] at hrange
      exact top_unique hrange
    let φ' : (show X.Modules from P) ⟶ M :=
      (sheafOfModulesEquivalence X).inverse.map φ
    exact epi_over_of_surjective_app φ' (U i) (hAffine i) hl

/-- The constructed generating family keeps its actual original global sections. -/
theorem generatingSectionsOfAffineSpans_top {I ι : Type u} (s : I → Γ(M, ⊤))
    (U : ι → X.Opens) (hAffine : ∀ i, IsAffineOpen (U i)) (hU : ⨆ i, U i = ⊤)
    (hspan : ∀ i, Submodule.span Γ(X, U i)
      (Set.range (fun a : I =>
        M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s a))) = ⊤) (a : I) :
    ((generatingSectionsOfAffineSpans M s U hAffine hU hspan).s a).val (op ⊤) = s a :=
  SheafOfModules.topSection_top M (s a)

/-- A finite family spanning on an affine cover gives native finite
generating sections with that same finite index type. -/
theorem generatingSectionsOfAffineSpans_isFiniteType {I ι : Type u} [Finite I]
    (s : I → Γ(M, ⊤)) (U : ι → X.Opens) (hAffine : ∀ i, IsAffineOpen (U i))
    (hU : ⨆ i, U i = ⊤)
    (hspan : ∀ i, Submodule.span Γ(X, U i)
      (Set.range (fun a : I =>
        M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s a))) = ⊤) :
    (generatingSectionsOfAffineSpans M s U hAffine hU hspan).IsFiniteType :=
  ⟨inferInstanceAs (Finite I)⟩

end AlgebraicGeometry.Scheme.Modules
