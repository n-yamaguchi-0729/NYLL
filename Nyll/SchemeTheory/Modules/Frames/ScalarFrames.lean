/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Invertible.UnitAutomorphisms
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Frames of a fixed module modulo scalars from the base

Two actual trivializations are identified precisely when their ratio
extends to a unit on the base scheme. Choosing one actual frame identifies
these classes with the quotient of units by base scalars. The classes
themselves do not assume a trivialization.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {Y S : Scheme.{u}} {M : Y.Modules}

/-- The actual unit carrying one trivialization of a fixed module to another. -/
def frameRatio (e f : M ≅ 𝟙_ Y.Modules) : Γ(Y, ⊤)ˣ :=
  unitAutEquivUnits Y (e.symm ≪≫ f)

theorem frameRatio_self (e : M ≅ 𝟙_ Y.Modules) : frameRatio e e = 1 := by
  have he : (e.symm ≪≫ e : Aut (𝟙_ Y.Modules)) = (1 : Aut (𝟙_ Y.Modules)) :=
    CategoryTheory.Iso.ext e.inv_hom_id
  exact (congrArg (unitAutEquivUnits Y) he).trans (map_one (unitAutEquivUnits Y))

/-- Composition of changes of frame is multiplication of their actual units. -/
theorem frameRatio_mul (e f g : M ≅ 𝟙_ Y.Modules) :
    frameRatio e f * frameRatio f g = frameRatio e g := by
  have he : ((e.symm ≪≫ f) ≪≫ (f.symm ≪≫ g) : Aut (𝟙_ Y.Modules)) =
      e.symm ≪≫ g := by
    apply CategoryTheory.Iso.ext
    change (e.inv ≫ f.hom) ≫ (f.inv ≫ g.hom) = e.inv ≫ g.hom
    rw [Category.assoc, f.hom_inv_id_assoc]
  exact (unitAutEquivUnits_isoTrans Y (e.symm ≪≫ f) (f.symm ≪≫ g)).symm.trans
    (congrArg (unitAutEquivUnits Y) he)

theorem frameRatio_symm (e f : M ≅ 𝟙_ Y.Modules) :
    frameRatio f e = (frameRatio e f)⁻¹ :=
  mul_eq_one_iff_eq_inv.mp ((frameRatio_mul f e f).trans (frameRatio_self f))

/-- Coordinates of a frame relative to one actual reference frame. -/
def frameCoordinates (e : M ≅ 𝟙_ Y.Modules) : (M ≅ 𝟙_ Y.Modules) ≃ Γ(Y, ⊤)ˣ where
  toFun := frameRatio e
  invFun a := e ≪≫ (unitAutEquivUnits Y).symm a
  left_inv f := by
    have he := (unitAutEquivUnits Y).symm_apply_apply (e.symm ≪≫ f)
    apply CategoryTheory.Iso.ext
    change e.hom ≫ ((unitAutEquivUnits Y).symm (frameRatio e f)).hom = f.hom
    exact (congrArg (fun a : Aut (𝟙_ Y.Modules) => e.hom ≫ a.hom) he).trans
      (e.hom_inv_id_assoc f.hom)
  right_inv a := by
    have he : (e.symm ≪≫ (e ≪≫ (unitAutEquivUnits Y).symm a) : Aut (𝟙_ Y.Modules)) =
        (unitAutEquivUnits Y).symm a :=
      CategoryTheory.Iso.ext (e.inv_hom_id_assoc _)
    exact (congrArg (unitAutEquivUnits Y) he).trans
      ((unitAutEquivUnits Y).apply_symm_apply a)

theorem frameRatio_eq_coordinates_div (e₀ e f : M ≅ 𝟙_ Y.Modules) :
    frameRatio e f = frameCoordinates e₀ f / frameCoordinates e₀ e := by
  apply eq_div_iff_mul_eq'.mpr
  rw [mul_comm]
  exact frameRatio_mul e₀ e f

/-- The scalar relation uses precisely the units that restrict from the base. -/
def scalarFrameSetoid (q : Y ⟶ S) (M : Y.Modules) : Setoid (M ≅ 𝟙_ Y.Modules) where
  r e f := frameRatio e f ∈ (Units.map q.appTop.hom.toMonoidHom).range
  iseqv := {
    refl := fun e => by
      rw [frameRatio_self]
      exact Subgroup.one_mem _
    symm := fun {e f} h => by
      rw [frameRatio_symm]
      exact Subgroup.inv_mem _ h
    trans := fun {e f g} h h' => by
      rw [← frameRatio_mul e f g]
      exact Subgroup.mul_mem _ h h' }

/-- Actual trivializations modulo the actual scalar relation from the base. -/
abbrev ScalarFrameClasses (q : Y ⟶ S) (M : Y.Modules) : Type u :=
  Quotient (scalarFrameSetoid q M)

/-- An explicit local trivialization identifies the frame quotient with
units modulo base scalars; it does not discard the chosen frame data. -/
def scalarFrameClassesEquiv (q : Y ⟶ S) (e₀ : M ≅ 𝟙_ Y.Modules) :
    ScalarFrameClasses q M ≃ Γ(Y, ⊤)ˣ ⧸ (Units.map q.appTop.hom.toMonoidHom).range := by
  refine Quotient.congr (frameCoordinates e₀) ?_
  intro e f
  constructor
  · intro h
    apply Quotient.exact
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [← frameRatio_eq_coordinates_div e₀ f e]
    exact (scalarFrameSetoid q M).symm h
  · intro h
    have he : (QuotientGroup.mk (frameCoordinates e₀ e) :
        Γ(Y, ⊤)ˣ ⧸ (Units.map q.appTop.hom.toMonoidHom).range) =
          QuotientGroup.mk (frameCoordinates e₀ f) := Quotient.sound h
    have hr := QuotientGroup.eq_iff_div_mem.mp he
    rw [← frameRatio_eq_coordinates_div e₀ f e] at hr
    exact (scalarFrameSetoid q M).symm hr

/-- Changing the actual reference frame translates the unit coordinates. -/
theorem frameCoordinates_change (e₀ e₁ e : M ≅ 𝟙_ Y.Modules) :
    frameCoordinates e₁ e = frameRatio e₁ e₀ * frameCoordinates e₀ e :=
  (frameRatio_mul e₁ e₀ e).symm

/-- The transition between local quotient coordinates is the class of the
actual ratio of reference frames. In particular it need not be the identity. -/
theorem scalarFrameClassesEquiv_change (q : Y ⟶ S)
    (e₀ e₁ : M ≅ 𝟙_ Y.Modules) (x : ScalarFrameClasses q M) :
    scalarFrameClassesEquiv q e₁ x =
      QuotientGroup.mk (frameRatio e₁ e₀) * scalarFrameClassesEquiv q e₀ x := by
  refine Quotient.inductionOn x fun e => ?_
  exact (congrArg QuotientGroup.mk (frameRatio_mul e₁ e₀ e)).symm

variable {N : Y.Modules}

/-- Transporting both frames through the same actual module isomorphism
leaves their ratio unchanged. -/
theorem frameRatio_precomp (a : N ≅ M) (e f : M ≅ 𝟙_ Y.Modules) :
    frameRatio (a ≪≫ e) (a ≪≫ f) = frameRatio e f := by
  have he : ((a ≪≫ e).symm ≪≫ (a ≪≫ f) : Aut (𝟙_ Y.Modules)) = e.symm ≪≫ f := by
    apply CategoryTheory.Iso.ext
    change (e.inv ≫ a.inv) ≫ (a.hom ≫ f.hom) = e.inv ≫ f.hom
    rw [Category.assoc, a.inv_hom_id_assoc]
  exact congrArg (unitAutEquivUnits Y) he

/-- Precomposition is the actual equivalence of frames of isomorphic modules. -/
def frameDomainEquiv (a : N ≅ M) : (M ≅ 𝟙_ Y.Modules) ≃ (N ≅ 𝟙_ Y.Modules) where
  toFun e := a ≪≫ e
  invFun e := a.symm ≪≫ e
  left_inv e := CategoryTheory.Iso.ext (a.inv_hom_id_assoc e.hom)
  right_inv e := CategoryTheory.Iso.ext (a.hom_inv_id_assoc e.hom)

/-- The frame quotient retains canonical identifications of the underlying
module, including those needed for pullback identity and composition. -/
def scalarFrameClassesCongr (q : Y ⟶ S) (a : N ≅ M) :
    ScalarFrameClasses q M ≃ ScalarFrameClasses q N := by
  refine Quotient.congr (frameDomainEquiv a) ?_
  intro e f
  change frameRatio e f ∈ _ ↔ frameRatio (a ≪≫ e) (a ≪≫ f) ∈ _
  rw [frameRatio_precomp]

end AlgebraicGeometry.Scheme.Modules
