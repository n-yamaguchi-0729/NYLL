/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedSquareEquivalence
import Nyll.JacobianVarieties.Generalized.PicardZeroGroupFunctor
import Nyll.JacobianVarieties.Picard.AlgebraicEquivalence.AlgebraicEquivalenceBaseChange
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-! # The actual rigidified classes at the identity test scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {X Z : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of R)) (i : Z ⟶ X)

/-- Identity base change identifies the full modulus inclusions. -/
theorem modulusIdentityBaseChange_square :
    modulusBaseChange c i (𝟙 (Spec (CommRingCat.of R))) ≫ pullback.fst c (𝟙 _) =
      pullback.fst (i ≫ c) (𝟙 _) ≫ i := by
  exact pullback.lift_fst _ _ _

/-- The identity test retains exactly the original specified rigidification. -/
def modulusIdentityBaseChangeClassesEquiv :
    RigidifiedLineBundle.Classes i ≃*
      RigidifiedLineBundle.Classes (modulusBaseChange c i (𝟙 (Spec (CommRingCat.of R)))) :=
  RigidifiedLineBundle.classesPullbackMulEquiv
    (asIso (pullback.fst c (𝟙 _))) (asIso (pullback.fst (i ≫ c) (𝟙 _)))
    (modulusIdentityBaseChange_square c i)

section Field

variable {K : Type u} [Field K] {Y Y' : Scheme.{u}}
  {a : Y ⟶ Spec (CommRingCat.of K)} {a' : Y' ⟶ Spec (CommRingCat.of K)}

/-- An actual isomorphism of curves reflects algebraic triviality of its pullback. -/
theorem isAlgEquivZero_pullback_iso_iff (e : Y' ≅ Y) (he : e.hom ≫ a = a')
    (L : Y.Modules) :
    RelPicard.IsAlgEquivZero a' ((Scheme.Modules.pullback e.hom).obj L) ↔
      RelPicard.IsAlgEquivZero a L := by
  constructor
  · intro h
    have hi : e.inv ≫ a' = a := by
      rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
    have hp := h.pullback e.inv hi
    let q : (Scheme.Modules.pullback e.inv).obj
        ((Scheme.Modules.pullback e.hom).obj L) ≅ L :=
      (Scheme.Modules.pullbackComp e.inv e.hom).app L ≪≫
        (Scheme.Modules.pullbackCongr e.inv_hom_id).app L ≪≫
        (Scheme.Modules.pullbackId Y).app L
    exact hp.of_iso q
  · exact fun h => h.pullback e.hom he

variable [IsAlgClosed K]

/-- Over an algebraically closed ground field the geometric-fibre condition
is equivalent to algebraic triviality of the original actual bundle. -/
theorem isAlgEquivZero_iff_geometricPullbacks (L : Y.Modules) :
    RelPicard.IsAlgEquivZero a L ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k]
        (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K)),
        RelPicard.IsAlgEquivZero (pullback.snd a s)
          ((Scheme.Modules.pullback (pullback.fst a s)).obj L) := by
  constructor
  · intro h k _ _ s
    let : Algebra K k := (Spec.preimage s).hom.toAlgebra
    have hs : Spec.map (CommRingCat.ofHom (algebraMap K k)) = s := by
      change Spec.map (Spec.preimage s) = s
      exact Spec.map_preimage s
    have hb := RelPicard.IsAlgEquivZero.baseChange k a h
    exact Eq.mp (congrArg (fun q : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K) =>
      RelPicard.IsAlgEquivZero (pullback.snd a q)
        ((Scheme.Modules.pullback (pullback.fst a q)).obj L)) hs) hb
  · intro h
    have he : pullback.fst a (𝟙 _) ≫ a = pullback.snd a (𝟙 _) :=
      (pullback.condition (f := a) (g := 𝟙 _)).trans (Category.comp_id _)
    exact (isAlgEquivZero_pullback_iso_iff (asIso (pullback.fst a (𝟙 _))) he L).mp
      (h K (𝟙 _))

end Field

section Zero

variable {K : Type u} [Field K] [IsAlgClosed K] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) (i : D ⟶ C)

/-- Identity base change preserves precisely the actual Picard-zero condition. -/
theorem modulusIdentityBaseChangeClassesEquiv_zero_iff
    (M : RigidifiedLineBundle i) :
    modulusIdentityBaseChangeClassesEquiv c i (RigidifiedLineBundle.classOf M) ∈
        modulusPicardZeroSubgroup c i (Over.mk (𝟙 (Spec (CommRingCat.of K)))) ↔
      RelPicard.IsAlgEquivZero c M.L := by
  let f := pullback.fst c (𝟙 (Spec (CommRingCat.of K)))
  let π := pullback.snd c (𝟙 (Spec (CommRingCat.of K)))
  change (∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K)),
      RelPicard.IsAlgEquivZero (pullback.snd π s)
        ((Scheme.Modules.pullback (pullback.fst π s)).obj
          ((Scheme.Modules.pullback f).obj M.L))) ↔ _
  have he : f ≫ c = π :=
    (pullback.condition (f := c) (g := 𝟙 _)).trans (Category.comp_id _)
  exact (isAlgEquivZero_iff_geometricPullbacks
    ((Scheme.Modules.pullback f).obj M.L)).symm.trans
      (isAlgEquivZero_pullback_iso_iff (asIso f) he M.L)

end Zero

end AlgebraicGeometry.GeneralizedJacobian
