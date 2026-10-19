/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusIsoComparison
import Nyll.JacobianVarieties.Generalized.PicardOneRestriction

/-! # Intrinsic Picard-one for isomorphic whole moduli -/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D D' : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) {i : D ⟶ C} {i' : D' ⟶ C}
  [IsClosedImmersion i] [IsClosedImmersion i'] (a : D' ≅ D) (w : i' = a.hom ≫ i)
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

omit [GeometricallyIntegral c] in
/-- The actual isomorphism of moduli preserves the intrinsic degree-one condition. -/
theorem modulusIsoClassesEquiv_one_iff {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R))
    (x : RigidifiedLineBundle.Classes (modulusBaseChange c i t)) :
    modulusIsoClassesEquiv c a w t x ∈
        (modulusPicardOneSubfunctor c i').obj (op (Over.mk t)) ↔
      x ∈ (modulusPicardOneSubfunctor c i).obj (op (Over.mk t)) := by
  constructor
  · intro hx
    have wi : i = a.inv ≫ i' := by
      rw [w, a.inv_hom_id_assoc]
    have h := (modulusRestrictionOneClasses c a.inv wi (Over.mk t)
      ⟨modulusIsoClassesEquiv c a w t x, hx⟩).property
    change (modulusIsoClassesEquiv c a w t).symm
      (modulusIsoClassesEquiv c a w t x) ∈
        (modulusPicardOneSubfunctor c i).obj (op (Over.mk t)) at h
    rw [MulEquiv.symm_apply_apply] at h
    exact h
  · intro hx
    exact (modulusRestrictionOneClasses c a.hom w (Over.mk t) ⟨x, hx⟩).property

/-- The equivalence retains the specified modulus frames on actual degree-one classes. -/
def modulusIsoOneClassesEquiv (T : Over (Spec (CommRingCat.of R))) :
    (modulusPicardOnePresheaf c i).obj (op T) ≃
      (modulusPicardOnePresheaf c i').obj (op T) where
  toFun x := ⟨modulusIsoClassesEquiv c a w T.hom x.val,
    (modulusIsoClassesEquiv_one_iff c a w T.hom x.val).mpr x.property⟩
  invFun y := ⟨(modulusIsoClassesEquiv c a w T.hom).symm y.val,
    (modulusIsoClassesEquiv_one_iff c a w T.hom _).mp (by
      erw [MulEquiv.apply_symm_apply]
      exact y.property)⟩
  left_inv x := Subtype.ext ((modulusIsoClassesEquiv c a w T.hom).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((modulusIsoClassesEquiv c a w T.hom).apply_symm_apply y.val)

/-- Natural comparison of intrinsic degree-one classes before sheafification. -/
def modulusPicardOneModulusIso :
    modulusPicardOnePresheaf c i ≅ modulusPicardOnePresheaf c i' :=
  NatIso.ofComponents (fun T => Equiv.toIso (modulusIsoOneClassesEquiv c a w T.unop))
    (fun {T T'} f => by
      apply TypeCat.homEquiv.injective
      funext x
      apply Subtype.ext
      exact modulusIsoClassesEquiv_naturality c a w f.unop x.val)

/-- The same comparison on the actual fppf sheaves. -/
def modulusPicardOneSheafModulusIso :
    modulusPicardOneSheaf c i ≅ modulusPicardOneSheaf c i' :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (Type (u + 1))).mapIso (modulusPicardOneModulusIso c a w)

omit [GeometricallyIntegral c] in
/-- The sheaf comparison classifies the actual isomorphism of rigidifications. -/
@[reassoc] theorem toSheafify_modulusPicardOneModulusIso :
    toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardOnePresheaf c i) ≫ (modulusPicardOneSheafModulusIso c a w).hom.hom =
      (modulusPicardOneModulusIso c a w).hom ≫
        toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
          (modulusPicardOnePresheaf c i') :=
  (toSheafify_naturality (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (modulusPicardOneModulusIso c a w).hom).symm

end AlgebraicGeometry.GeneralizedJacobian
