/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardForgetful
import Nyll.SchemeTheory.Modules.Sections.SectionsGluing
import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.Unrigidified
import Nyll.AlgebraicCurves.Geometry.Schemes.RigidifiedLineBundleOfInvertible
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Logic.Relation

/-!
# Empty modulus and ordinary relative line bundles

On an empty scheme every section and every module morphism is unique. Consequently
every actual underlying line bundle has a unique chosen rigidification on an empty
modulus, and every underlying isomorphism is compatible. A base twist is then shown
to disappear after any actual trivialization of its base line bundle.
-/

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

noncomputable section

namespace AlgebraicGeometry.GeneralizedJacobian.EmptyModulus

/-- Uniqueness of sections on an empty scheme is a consequence of the empty-cover
separatedness condition, not an extra assumption about module sections. -/
theorem section_eq {E : Scheme.{u}} [IsEmpty E] (M : E.Modules) (U : E.Opens)
    (s t : Γ(M, U)) : s = t := by
  exact (Scheme.Modules.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible M
    (fun _ : PEmpty.{u + 1} => (⊥ : E.Opens)) U (fun _ => bot_le)
    (by intro x hx; exact isEmptyElim x)).1 s t (fun e => isEmptyElim e)

/-- Every pair of module maps over an empty scheme agrees. -/
theorem module_hom_eq {E : Scheme.{u}} [IsEmpty E] {M N : E.Modules}
    (f g : M ⟶ N) : f = g := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  exact section_eq N U _ _

/-- The unique isomorphism between any two module sheaves on an empty scheme. -/
def moduleIso {E : Scheme.{u}} [IsEmpty E] (M N : E.Modules) : M ≅ N where
  hom := 0
  inv := 0
  hom_inv_id := module_hom_eq _ _
  inv_hom_id := module_hom_eq _ _

theorem moduleIso_unique {E : Scheme.{u}} [IsEmpty E] {M N : E.Modules}
    (e e' : M ≅ N) : e = e' := by
  apply CategoryTheory.Iso.ext
  exact module_hom_eq _ _

/-- Every actual invertible module has the unique rigidification on an empty modulus. -/
def rigidify {X E : Scheme.{u}} [IsEmpty E] (i : E ⟶ X)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) : RigidifiedLineBundle i where
  L := L
  isInvertible := hL
  trivialization := moduleIso ((Scheme.Modules.pullback i).obj L) (𝟙_ E.Modules)

/-- Under empty modulus, compatibility is a theorem for any actual underlying isomorphism. -/
def compatibleIso {X E : Scheme.{u}} [IsEmpty E] {i : E ⟶ X}
    {M N : RigidifiedLineBundle i} (e : M.L ≅ N.L) : RigidifiedLineBundle.Iso M N where
  toIso := e
  compatible := module_hom_eq _ _

variable {R : Type u} [CommRing R] {X D : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of R)) (i : D ⟶ X) [IsEmpty D]

private instance empty_baseChange {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    IsEmpty (pullback (i ≫ c) t : Scheme.{u}) :=
  Function.isEmpty (fun x : (pullback (i ≫ c) t : Scheme.{u}) =>
    (pullback.fst (i ≫ c) t) x)

/-- Canonical chosen rigidification of an arbitrary actual relative line bundle. -/
def ofLineBundle {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RelPicard.Unrigidified.LineBundle c t) :
    RigidifiedLineBundle (modulusBaseChange c i t) :=
  rigidify (modulusBaseChange c i t) M.1 M.2

/-- Any supplied empty-modulus rigidification is compatibly isomorphic to the canonical one. -/
def ofLineBundleIso {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle (modulusBaseChange c i t)) :
    RigidifiedLineBundle.Iso M
      (ofLineBundle c i (⟨M.L, M.isInvertible⟩ : RelPicard.Unrigidified.LineBundle c t)) :=
  compatibleIso (CategoryTheory.Iso.refl M.L)

/-- Forgetting an empty modulus is surjective on relative quotient classes. It is
not asserted to be injective before sheafification. -/
theorem forgetModulusClasses_surjective {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    Function.Surjective (forgetModulusClasses c i t) := by
  intro x
  induction x using Quot.ind with
  | _ M => exact ⟨RigidifiedLineBundle.classOf (ofLineBundle c i M), rfl⟩

/-- Pointwise surjectivity supplies the local-surjectivity half of the comparison. -/
theorem forgetModulusPresheaf_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (forgetModulusPresheaf c i) :=
  Presheaf.isLocallySurjective_of_surjective
    (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (forgetModulusPresheaf c i)
    (fun T => forgetModulusClasses_surjective c i T.unop.hom)

end AlgebraicGeometry.GeneralizedJacobian.EmptyModulus

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  {c : X ⟶ Spec (CommRingCat.of R)}

/-- A base twist becomes an actual isomorphism on any scheme where the particular
base line bundle has an actual trivialization. No quotient equality is assumed. -/
def baseTwistPullbackIso {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (s : NeronModelInfra.SchemeHomOver t' t)
    (M N : RelPicard.Unrigidified.LineBundle c t) (Q : T.Modules)
    (e : N.1 ≅ (Scheme.Modules.pullback (pullback.snd c t)).obj Q ⊗ M.1)
    (v : (Scheme.Modules.pullback s.1).obj Q ≅ 𝟙_ T'.Modules) :
    (RelPicard.Unrigidified.pullbackAlong s N).1 ≅
      (RelPicard.Unrigidified.pullbackAlong s M).1 :=
  (Scheme.Modules.pullback (RelPicard.baseChangeSnd c s)).mapIso e ≪≫
    Scheme.Modules.pullbackTensorObjIso (RelPicard.baseChangeSnd c s)
      ((Scheme.Modules.pullback (pullback.snd c t)).obj Q) M.1 ≪≫
    (((Scheme.Modules.pullbackComp (RelPicard.baseChangeSnd c s) (pullback.snd c t)).app Q ≪≫
      (Scheme.Modules.pullbackCongr (RelPicard.baseChangeSnd_snd s)).app Q ≪≫
      ((Scheme.Modules.pullbackComp (pullback.snd c t') s.1).app Q).symm ≪≫
      (Scheme.Modules.pullback (pullback.snd c t')).mapIso v ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso (pullback.snd c t')) ⊗ᵢ
        CategoryTheory.Iso.refl
          ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c s)).obj M.1)) ≪≫
    λ_ ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c s)).obj M.1)

end AlgebraicGeometry.GeneralizedJacobian
