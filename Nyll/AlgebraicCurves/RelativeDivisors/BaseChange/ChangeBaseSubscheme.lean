/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.RelativeDivisors.BaseChange.ChangeBase

/-! # The whole divisor subscheme under change of the curve's base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RelEffCartierDiv

variable {C S S' T : Scheme.{u}} (f : C ⟶ S) (s : S' ⟶ S) (g : T ⟶ S') {r : ℕ}

/-- The actual subscheme map induced by the pullback associativity isomorphism. -/
def changeBaseEquivSubschemeMap (D : RelEffCartierDiv f r (g ≫ s)) :
    ((changeBaseEquiv f s g r).symm D).I.subscheme ⟶ D.I.subscheme :=
  (D.I.comapIso (pullbackLeftPullbackSndIso f s g).hom).hom ≫ pullback.snd _ _

/-- The defining ideal, including its nilpotents, is pulled back along the same square. -/
theorem changeBaseEquivSubscheme_isPullback (D : RelEffCartierDiv f r (g ≫ s)) :
    IsPullback (changeBaseEquivSubschemeMap f s g D)
      ((changeBaseEquiv f s g r).symm D).I.subschemeι D.I.subschemeι
      (pullbackLeftPullbackSndIso f s g).hom := by
  refine (IsPullback.of_iso_pullback ⟨?_⟩
    (D.I.comapIso (pullbackLeftPullbackSndIso f s g).hom) ?_ ?_).flip
  · change (D.I.comap (pullbackLeftPullbackSndIso f s g).hom).subschemeι ≫
        (pullbackLeftPullbackSndIso f s g).hom =
      ((D.I.comapIso (pullbackLeftPullbackSndIso f s g).hom).hom ≫ pullback.snd _ _) ≫ _
    rw [Category.assoc, ← pullback.condition, D.I.comapIso_hom_fst_assoc]
  · exact D.I.comapIso_hom_fst _
  · rfl

/-- The same square identifies the finite flat maps to the parameter scheme. -/
theorem changeBaseEquivSubscheme_snd_isPullback (D : RelEffCartierDiv f r (g ≫ s)) :
    IsPullback (changeBaseEquivSubschemeMap f s g D)
      (((changeBaseEquiv f s g r).symm D).I.subschemeι ≫
        pullback.snd (pullback.snd f s) g)
      (D.I.subschemeι ≫ pullback.snd f (g ≫ s)) (𝟙 T) := by
  apply (changeBaseEquivSubscheme_isPullback f s g D).paste_vert
  exact IsPullback.of_horiz_isIso
    ⟨(pullbackLeftPullbackSndIso_hom_snd f s g).trans (Category.comp_id _).symm⟩

variable {f} (D : RelEffCartierDiv f r (𝟙 S))

/-- Scalar extension of a divisor defined on the curve itself. -/
def changeBaseOfIdentity : RelEffCartierDiv (pullback.snd f s) r (𝟙 S') :=
  (changeBaseEquiv f s (𝟙 S') r).symm
    (D.pullbackAlong s (by rw [Category.comp_id, Category.id_comp]))

/-- The map of whole modulus subschemes, before passing to supports or points. -/
def changeBaseOfIdentityMap : (changeBaseOfIdentity s D).I.subscheme ⟶ D.I.subscheme :=
  changeBaseEquivSubschemeMap f s (𝟙 S')
      (D.pullbackAlong s (by rw [Category.comp_id, Category.id_comp])) ≫
    comapSubschemeMapOver D.I s (by rw [Category.comp_id, Category.id_comp])

/-- The new whole modulus is the actual base change of the original finite scheme. -/
theorem changeBaseOfIdentity_isPullback :
    IsPullback (changeBaseOfIdentityMap s D)
      ((changeBaseOfIdentity s D).I.subschemeι ≫ pullback.snd (pullback.snd f s) (𝟙 S'))
      (D.I.subschemeι ≫ pullback.snd f (𝟙 S)) s := by
  dsimp only [changeBaseOfIdentity, changeBaseOfIdentityMap]
  simpa only [Category.id_comp] using
    (changeBaseEquivSubscheme_snd_isPullback f s (𝟙 S')
      (D.pullbackAlong s (by rw [Category.comp_id, Category.id_comp]))).paste_horiz
        (isPullback_comap_snd_over D.I s (by rw [Category.comp_id, Category.id_comp]))

/-- Canonical isomorphism of the full scalar-extended divisor with the scheme pullback. -/
def changeBaseOfIdentitySubschemeIso :
    (changeBaseOfIdentity s D).I.subscheme ≅
      pullback (D.I.subschemeι ≫ pullback.snd f (𝟙 S)) s :=
  (changeBaseOfIdentity_isPullback s D).isoPullback

@[reassoc] theorem changeBaseOfIdentitySubschemeIso_hom_fst :
    (changeBaseOfIdentitySubschemeIso s D).hom ≫
        pullback.fst (D.I.subschemeι ≫ pullback.snd f (𝟙 S)) s =
      changeBaseOfIdentityMap s D :=
  (changeBaseOfIdentity_isPullback s D).isoPullback_hom_fst

@[reassoc] theorem changeBaseOfIdentitySubschemeIso_hom_snd :
    (changeBaseOfIdentitySubschemeIso s D).hom ≫
        pullback.snd (D.I.subschemeι ≫ pullback.snd f (𝟙 S)) s =
      (changeBaseOfIdentity s D).I.subschemeι ≫ pullback.snd (pullback.snd f s) (𝟙 S') :=
  (changeBaseOfIdentity_isPullback s D).isoPullback_hom_snd

/-- Its inclusion into the curve agrees with the base-changed original inclusion. -/
@[reassoc] theorem changeBaseOfIdentityMap_curve :
    changeBaseOfIdentityMap s D ≫ D.I.subschemeι ≫ pullback.fst f (𝟙 S) =
      (changeBaseOfIdentity s D).I.subschemeι ≫
        pullback.fst (pullback.snd f s) (𝟙 S') ≫ pullback.fst f s := by
  let w : s ≫ 𝟙 S = 𝟙 S' ≫ s := by rw [Category.comp_id, Category.id_comp]
  let E := D.pullbackAlong s w
  let a := changeBaseEquivSubschemeMap f s (𝟙 S') E
  let b : E.I.subscheme ⟶ D.I.subscheme := comapSubschemeMapOver D.I s w
  have hb : b ≫ D.I.subschemeι ≫ pullback.fst f (𝟙 S) =
      E.I.subschemeι ≫ pullback.fst f (𝟙 S' ≫ s) := by
    exact ((isPullback_comapSubschemeMapOver D.I s w).w_assoc _).trans
      (congrArg (E.I.subschemeι ≫ ·) (mapOnProdOver_fst f s w))
  have ha := (changeBaseEquivSubscheme_isPullback f s (𝟙 S') E).w
  change (a ≫ b) ≫ D.I.subschemeι ≫ pullback.fst f (𝟙 S) = _
  calc
    _ = a ≫ E.I.subschemeι ≫ pullback.fst f (𝟙 S' ≫ s) :=
      (Category.assoc _ _ _).trans (congrArg (a ≫ ·) hb)
    _ = ((changeBaseEquiv f s (𝟙 S') r).symm E).I.subschemeι ≫
        (pullbackLeftPullbackSndIso f s (𝟙 S')).hom ≫
          pullback.fst f (𝟙 S' ≫ s) := by
      rw [← Category.assoc, ha, Category.assoc]
    _ = _ := congrArg (_ ≫ ·) (pullbackLeftPullbackSndIso_hom_fst f s (𝟙 S'))

end AlgebraicGeometry.RelEffCartierDiv
