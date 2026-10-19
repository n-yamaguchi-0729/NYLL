/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Modules.Frames.Frames
import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Frame coordinates with the original base module structures

A frame identifies actual module-sheaf sections with structure-sheaf
sections. This identification is linear over the affine base through
the original structural morphism, and it commutes with restriction.
Both sides use exactly the section modules supplied to the native
sheaf-to-Čech construction.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) {M : X.Modules} {U V W : X.Opens}

/-- Multiplication by an actual local section, retaining the original
base scalar actions on both section modules. -/
def frameSectionLinearMap (s : Γ(M, U)) (hWU : W ≤ U) :
    (OModulePresheaf.unit f).obj W →ₗ[R] sectionModuleOverBase f M W where
  toFun a := (show Γ(X, W) from a) • M.presheaf.map (homOfLE hWU).op s
  map_add' a b := add_smul (show Γ(X, W) from a) (show Γ(X, W) from b)
    (M.presheaf.map (homOfLE hWU).op s)
  map_smul' r a := by
    change ((f.constToPresheaf.app (op W)).hom r * (show Γ(X, W) from a)) •
        M.presheaf.map (homOfLE hWU).op s =
      (f.constToPresheaf.app (op W)).hom r •
        ((show Γ(X, W) from a) • M.presheaf.map (homOfLE hWU).op s)
    exact mul_smul _ _ _

/-- An actual frame gives a linear equivalence over the original base. -/
def IsFrameOn.sectionEquivOverBase {s : Γ(M, U)} (hs : IsFrameOn s V)
    (hWU : W ≤ U) (hWV : W ≤ V) :
    (OModulePresheaf.unit f).obj W ≃ₗ[R] sectionModuleOverBase f M W :=
  LinearEquiv.ofBijective (frameSectionLinearMap f s hWU) (hs hWU hWV)

theorem IsFrameOn.sectionEquivOverBase_apply {s : Γ(M, U)} (hs : IsFrameOn s V)
    (hWU : W ≤ U) (hWV : W ≤ V) (a : (OModulePresheaf.unit f).obj W) :
    hs.sectionEquivOverBase f hWU hWV a =
      (show Γ(X, W) from a) • M.presheaf.map (homOfLE hWU).op s := rfl

/-- Frame coordinates commute with the original restrictions on both
the structure sheaf and the module sheaf. -/
theorem IsFrameOn.sectionEquivOverBase_restrict {s : Γ(M, U)} (hs : IsFrameOn s V)
    (hWU : W ≤ U) (hWV : W ≤ V) {W' : X.Opens} (h : W' ≤ W)
    (a : (OModulePresheaf.unit f).obj W) :
    sectionRestrictionOverBase f M h (hs.sectionEquivOverBase f hWU hWV a) =
      hs.sectionEquivOverBase f (h.trans hWU) (h.trans hWV)
        ((OModulePresheaf.unit f).res h a) := by
  change M.presheaf.map (homOfLE h).op
      ((show Γ(X, W) from a) • M.presheaf.map (homOfLE hWU).op s) =
    X.presheaf.map (homOfLE h).op (show Γ(X, W) from a) •
      M.presheaf.map (homOfLE (h.trans hWU)).op s
  rw [M.map_smul]
  apply congrArg (fun m : Γ(M, W') =>
    X.presheaf.map (homOfLE h).op (show Γ(X, W) from a) • m)
  exact (congrArg (fun k : Γ(M, U) ⟶ Γ(M, W') => k s)
    (M.presheaf.map_comp (homOfLE hWU).op (homOfLE h).op)).symm

end AlgebraicGeometry.Scheme.Modules
