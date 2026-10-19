/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedLineBundle
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.SectionZeroScheme
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleComapZeroSchemeIdeal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Frames.InvertibleIsFrameOnApp
import Nyll.SchemeTheory.Modules.Frames.FrameLocality
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealInvertibleInvModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealZeroSchemeIdealInvModuleSection
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Canonical rigidification of an effective Cartier divisor away from the modulus

The inverse ideal module has its actual canonical section. If the image of the
modulus avoids the divisor support, this section pulls back to a frame on the
entire modulus. The resulting isomorphism is inverted to obtain the chosen
trivialization. Thus the trivialization sends the canonical section to one,
including on the nonreduced modulus; it is not chosen from an arbitrary
nonempty type of module isomorphisms.

This file does not yet identify divisor classes with the modulus Picard sheaf,
nor prove compatibility with addition or modulus-principal divisors.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {X D : Scheme.{u}} (i : D ⟶ X)

/-- Avoiding the zero support makes the actual pulled section invertible.
The proof uses its zero-scheme ideal and the existing local-frame criterion. -/
private theorem isIso_pullbackSection_of_avoids_support
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ M)
    (havoid : ∀ y : D, i.base y ∉ (zeroSchemeIdeal s).support) :
    IsIso (pullbackSection i s) := by
  have hpull : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback i).obj M) :=
    hM.pullback i
  have hdisjoint : Disjoint ((⊤ : D.Opens) : Set D)
      ((zeroSchemeIdeal (pullbackSection i s)).support : Set D) := by
    rw [← Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal i hM s,
      Scheme.IdealSheafData.support_comap]
    exact Set.disjoint_left.mpr (fun y _ hy => havoid y hy)
  have hframe : IsFrameOn
      ((pullbackSection i s).app ⊤ (toUnitSection ⊤ 1)) (⊤ : D.Opens) :=
    hpull.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
      (pullbackSection i s) ⊤ hdisjoint
  exact Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top
    (pullbackSection i s) (fun _ : Unit => (⊤ : D.Opens))
    iSup_const
    (fun _ => unitSection (⊤ : D.Opens))
    (fun _ => (pullbackSection i s).app ⊤ (toUnitSection ⊤ 1))
    (fun _ => isFrameOn_unitSection (X := D) (U := ⊤) ⊤)
    (fun _ => hframe) (fun _ => rfl)

/-- Trivialize the restriction by declaring the given nowhere-vanishing
pulled section to be one. -/
def sectionRestrictionIso {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ M)
    (havoid : ∀ y : D, i.base y ∉ (zeroSchemeIdeal s).support) :
    (Scheme.Modules.pullback i).obj M ≅ 𝟙_ D.Modules := by
  let hsection : IsIso (pullbackSection i s) :=
    isIso_pullbackSection_of_avoids_support i hM s havoid
  exact (asIso (pullbackSection i s)).symm

/-- The inverse trivialization is the specified section, rather than an
arbitrary isomorphism from the structure sheaf. -/
@[simp] theorem sectionRestrictionIso_inv
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ M)
    (havoid : ∀ y : D, i.base y ∉ (zeroSchemeIdeal s).support) :
    (sectionRestrictionIso i hM s havoid).inv = pullbackSection i s := rfl

/-- The chosen trivialization takes the canonical pulled section to one. -/
@[reassoc] theorem sectionRestrictionIso_section
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ M)
    (havoid : ∀ y : D, i.base y ∉ (zeroSchemeIdeal s).support) :
    pullbackSection i s ≫ (sectionRestrictionIso i hM s havoid).hom =
      𝟙 (𝟙_ D.Modules) :=
  (sectionRestrictionIso i hM s havoid).inv_hom_id

/-- The actual inverse-ideal line bundle with its canonical trivialization
along a disjoint modulus. The scheme `D` retains its full structure. -/
def ofInvertibleIdeal (I : X.IdealSheafData) (hI : I.IsInvertible)
    (havoid : ∀ y : D, i.base y ∉ I.support) : RigidifiedLineBundle i where
  L := I.invModule
  isInvertible := hI.isInvertible_invModule
  trivialization := sectionRestrictionIso i hI.isInvertible_invModule I.invModuleSection
    (fun y => by
      rw [hI.zeroSchemeIdeal_invModuleSection]
      exact havoid y)

/-- The inverse rigidification is the pullback of the actual canonical section
of the inverse ideal. -/
@[simp] theorem ofInvertibleIdeal_trivialization_inv
    (I : X.IdealSheafData) (hI : I.IsInvertible)
    (havoid : ∀ y : D, i.base y ∉ I.support) :
    (ofInvertibleIdeal i I hI havoid).trivialization.inv =
      pullbackSection i I.invModuleSection := rfl

/-- The canonical divisor section becomes one under the chosen rigidification. -/
@[reassoc] theorem ofInvertibleIdeal_section
    (I : X.IdealSheafData) (hI : I.IsInvertible)
    (havoid : ∀ y : D, i.base y ∉ I.support) :
    pullbackSection i I.invModuleSection ≫
      (ofInvertibleIdeal i I hI havoid).trivialization.hom = 𝟙 (𝟙_ D.Modules) :=
  (ofInvertibleIdeal i I hI havoid).trivialization.inv_hom_id

/-- Sending the canonical section to one uniquely specifies the trivialization. -/
theorem ofInvertibleIdeal_trivialization_unique
    (I : X.IdealSheafData) (hI : I.IsInvertible)
    (havoid : ∀ y : D, i.base y ∉ I.support)
    (e : (Scheme.Modules.pullback i).obj I.invModule ≅ 𝟙_ D.Modules)
    (he : pullbackSection i I.invModuleSection ≫ e.hom = 𝟙 (𝟙_ D.Modules)) :
    e = (ofInvertibleIdeal i I hI havoid).trivialization := by
  apply CategoryTheory.Iso.ext
  apply (cancel_epi (ofInvertibleIdeal i I hI havoid).trivialization.inv).mp
  rw [ofInvertibleIdeal_trivialization_inv]
  exact he.trans (ofInvertibleIdeal_section i I hI havoid).symm

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
