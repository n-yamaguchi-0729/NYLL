/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperHenselianActionPullback
public import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
public import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackIdentity

/-!
# The native descent comparison of a pulled-back finite étale cover

All comparisons preserve the projection to the original covering scheme.
No geometric hypothesis on the base map is required.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

open ProperHenselianActionLifting

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

variable {X Y T U : Scheme.{u}} (q : Y ⟶ X) (Z : FiniteEtale X)

/-- Compare the two iterated pullbacks through their common composite. -/
def pullbackDescentComparison (a b : T ⟶ Y) (hab : a ≫ q = b ≫ q) :
    (FiniteEtale.pullback a).obj ((FiniteEtale.pullback q).obj Z) ≅
      (FiniteEtale.pullback b).obj ((FiniteEtale.pullback q).obj Z) :=
  ((MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) a q (a ≫ q) rfl).app Z).symm ≪≫
    (MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤) b q (a ≫ q) hab).app Z

/-- The comparison retains the original covering-scheme projection. -/
theorem pullbackDescentComparison_hom_left_fst_fst
    (a b : T ⟶ Y) (hab : a ≫ q = b ≫ q) :
    (pullbackDescentComparison q Z a b hab).hom.left ≫
        Limits.pullback.fst ((FiniteEtale.pullback q).obj Z).hom b ≫
          Limits.pullback.fst Z.hom q =
      Limits.pullback.fst ((FiniteEtale.pullback q).obj Z).hom a ≫
        Limits.pullback.fst Z.hom q := by
  let w : Limits.pullback Z.hom q ⟶ Y := Limits.pullback.snd Z.hom q
  let ca := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) a q (a ≫ q) rfl).app Z
  let cb := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) b q (a ≫ q) hab).app Z
  let fa : Limits.pullback w a ⟶ Limits.pullback Z.hom (a ≫ q) := ca.inv.left
  let fb : Limits.pullback Z.hom (a ≫ q) ⟶ Limits.pullback w b := cb.hom.left
  let rb : Limits.pullback w b ⟶ Limits.pullback Z.hom q := Limits.pullback.fst w b
  let rz : Limits.pullback Z.hom q ⟶ Z.left := Limits.pullback.fst Z.hom q
  let r : Limits.pullback Z.hom (a ≫ q) ⟶ Z.left :=
    Limits.pullback.fst Z.hom (a ≫ q)
  have hb : fb ≫ rb ≫ rz = r :=
    pullbackComp_hom_app_left_fst_fst b q (a ≫ q) hab Z
  have ha : fa ≫ r = Limits.pullback.fst w a ≫ rz :=
    pullbackComp_inv_app_left_fst a q (a ≫ q) rfl Z
  change (fa ≫ fb) ≫ rb ≫ rz = Limits.pullback.fst w a ≫ rz
  exact (Category.assoc fa fb (rb ≫ rz)).trans
    ((congrArg (fun k => fa ≫ k) hb).trans ha)

/-- The actual overlap comparison of the pullback of `Z`. -/
def canonicalPullbackDescentIso :
    (FiniteEtale.pullback (Limits.pullback.fst q q)).obj
        ((FiniteEtale.pullback q).obj Z) ≅
      (FiniteEtale.pullback (Limits.pullback.snd q q)).obj
        ((FiniteEtale.pullback q).obj Z) :=
  pullbackDescentComparison q Z (Limits.pullback.fst q q)
    (Limits.pullback.snd q q) Limits.pullback.condition

/-- Reindexing the canonical comparison retains the original projection. -/
theorem canonicalPullbackDescentIso_reindex_hom_left_fst_fst
    (h : T ⟶ Limits.pullback q q) (a b : T ⟶ Y)
    (ha : a = h ≫ Limits.pullback.fst q q)
    (hb : b = h ≫ Limits.pullback.snd q q) :
    (reindexIso ((FiniteEtale.pullback q).obj Z)
        (canonicalPullbackDescentIso q Z) h a b ha hb).hom.left ≫
        Limits.pullback.fst ((FiniteEtale.pullback q).obj Z).hom b ≫
          Limits.pullback.fst Z.hom q =
      Limits.pullback.fst ((FiniteEtale.pullback q).obj Z).hom a ≫
        Limits.pullback.fst Z.hom q := by
  let W := (FiniteEtale.pullback q).obj Z
  let w : W.left ⟶ Y := W.hom
  let u : Limits.pullback q q ⟶ Y := Limits.pullback.fst q q
  let v : Limits.pullback q q ⟶ Y := Limits.pullback.snd q q
  let z : W.left ⟶ Z.left := Limits.pullback.fst Z.hom q
  let pa : Limits.pullback w a ⟶ W.left := Limits.pullback.fst w a
  let pb : Limits.pullback w b ⟶ W.left := Limits.pullback.fst w b
  let pu : Limits.pullback w u ⟶ W.left := Limits.pullback.fst w u
  let pv : Limits.pullback w v ⟶ W.left := Limits.pullback.fst w v
  let r : Limits.pullback (Limits.pullback.snd w u) h ⟶ Limits.pullback w u :=
    Limits.pullback.fst (Limits.pullback.snd w u) h
  let d : Limits.pullback w u ⟶ Limits.pullback w v :=
    (canonicalPullbackDescentIso q Z).hom.left
  let L : Limits.pullback w a ⟶ Limits.pullback (Limits.pullback.snd w u) h :=
    ((MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤) h u a ha).hom.app W).left
  let K : Limits.pullback w a ⟶ Limits.pullback w b :=
    (reindexIso W (canonicalPullbackDescentIso q Z) h a b ha hb).hom.left
  have hθ : d ≫ pv ≫ z = pu ≫ z :=
    pullbackDescentComparison_hom_left_fst_fst q Z u v Limits.pullback.condition
  have hc : L ≫ r ≫ pu = pa :=
    pullbackComp_hom_app_left_fst_fst h u a ha W
  have hK : K ≫ pb = L ≫ r ≫ d ≫ pv :=
    reindexIso_hom_left_fst W (canonicalPullbackDescentIso q Z) h a b ha hb
  change K ≫ pb ≫ z = pa ≫ z
  calc
    _ = (K ≫ pb) ≫ z := (Category.assoc K pb z).symm
    _ = (L ≫ r ≫ d ≫ pv) ≫ z := congrArg (fun k => k ≫ z) hK
    _ = L ≫ r ≫ (d ≫ pv ≫ z) := by simp only [Category.assoc]
    _ = L ≫ r ≫ (pu ≫ z) := congrArg (fun k => L ≫ r ≫ k) hθ
    _ = (L ≫ r ≫ pu) ≫ z := by simp only [Category.assoc]
    _ = _ := congrArg (fun k => k ≫ z) hc

/-- A morphism between the two iterated pullbacks is determined by its
projection to the original covering scheme. -/
theorem pullbackDescent_hom_ext
    (a b : T ⟶ Y)
    {f g : (FiniteEtale.pullback a).obj ((FiniteEtale.pullback q).obj Z) ⟶
      (FiniteEtale.pullback b).obj ((FiniteEtale.pullback q).obj Z)}
    (h : f.left ≫ Limits.pullback.fst ((FiniteEtale.pullback q).obj Z).hom b ≫
          Limits.pullback.fst Z.hom q =
        g.left ≫ Limits.pullback.fst ((FiniteEtale.pullback q).obj Z).hom b ≫
          Limits.pullback.fst Z.hom q) : f = g := by
  let W := (FiniteEtale.pullback q).obj Z
  let w : W.left ⟶ Y := W.hom
  let rb : Limits.pullback w b ⟶ W.left := Limits.pullback.fst w b
  let sb : Limits.pullback w b ⟶ T := Limits.pullback.snd w b
  let f₀ : Limits.pullback w a ⟶ Limits.pullback w b := f.left
  let g₀ : Limits.pullback w a ⟶ Limits.pullback w b := g.left
  have hc : rb ≫ w = sb ≫ b := Limits.pullback.condition
  have hfg : f₀ ≫ sb = g₀ ≫ sb := f.w.trans g.w.symm
  apply MorphismProperty.Over.Hom.ext
  apply Limits.pullback.hom_ext
  · apply Limits.pullback.hom_ext
    · exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
    · change (f₀ ≫ rb) ≫ w = (g₀ ≫ rb) ≫ w
      calc
        _ = f₀ ≫ (rb ≫ w) := Category.assoc f₀ rb w
        _ = f₀ ≫ (sb ≫ b) := congrArg (fun k => f₀ ≫ k) hc
        _ = (f₀ ≫ sb) ≫ b := (Category.assoc f₀ sb b).symm
        _ = (g₀ ≫ sb) ≫ b := congrArg (fun k => k ≫ b) hfg
        _ = g₀ ≫ (sb ≫ b) := Category.assoc g₀ sb b
        _ = g₀ ≫ (rb ≫ w) := congrArg (fun k => g₀ ≫ k) hc.symm
        _ = _ := (Category.assoc g₀ rb w).symm
  · exact f.w.trans g.w.symm

/-- The canonical native comparison satisfies the cocycle on every
compatible triple, hence on the actual threefold fibre product. -/
theorem canonicalPullbackDescentIso_cocycle
    (a b c : T ⟶ Y) (hab : a ≫ q = b ≫ q) (hbc : b ≫ q = c ≫ q) :
    let W := (FiniteEtale.pullback q).obj Z
    let θ := canonicalPullbackDescentIso q Z
    reindexIso W θ (Limits.pullback.lift a b hab) a b
        (Limits.pullback.lift_fst _ _ _).symm
        (Limits.pullback.lift_snd _ _ _).symm ≪≫
      reindexIso W θ (Limits.pullback.lift b c hbc) b c
        (Limits.pullback.lift_fst _ _ _).symm
        (Limits.pullback.lift_snd _ _ _).symm =
    reindexIso W θ (Limits.pullback.lift a c (hab.trans hbc)) a c
      (Limits.pullback.lift_fst _ _ _).symm
      (Limits.pullback.lift_snd _ _ _).symm := by
  intro W θ
  let w : W.left ⟶ Y := W.hom
  let ra : Limits.pullback w a ⟶ Z.left :=
    Limits.pullback.fst w a ≫ Limits.pullback.fst Z.hom q
  let rb : Limits.pullback w b ⟶ Z.left :=
    Limits.pullback.fst w b ≫ Limits.pullback.fst Z.hom q
  let rc : Limits.pullback w c ⟶ Z.left :=
    Limits.pullback.fst w c ≫ Limits.pullback.fst Z.hom q
  let ab : Limits.pullback w a ⟶ Limits.pullback w b :=
    (reindexIso W θ (Limits.pullback.lift a b hab) a b
      (Limits.pullback.lift_fst _ _ _).symm
      (Limits.pullback.lift_snd _ _ _).symm).hom.left
  let bc : Limits.pullback w b ⟶ Limits.pullback w c :=
    (reindexIso W θ (Limits.pullback.lift b c hbc) b c
      (Limits.pullback.lift_fst _ _ _).symm
      (Limits.pullback.lift_snd _ _ _).symm).hom.left
  let ac : Limits.pullback w a ⟶ Limits.pullback w c :=
    (reindexIso W θ (Limits.pullback.lift a c (hab.trans hbc)) a c
      (Limits.pullback.lift_fst _ _ _).symm
      (Limits.pullback.lift_snd _ _ _).symm).hom.left
  have h₁ : ab ≫ rb = ra := canonicalPullbackDescentIso_reindex_hom_left_fst_fst
    q Z (Limits.pullback.lift a b hab) a b
      (Limits.pullback.lift_fst _ _ _).symm (Limits.pullback.lift_snd _ _ _).symm
  have h₂ : bc ≫ rc = rb := canonicalPullbackDescentIso_reindex_hom_left_fst_fst
    q Z (Limits.pullback.lift b c hbc) b c
      (Limits.pullback.lift_fst _ _ _).symm (Limits.pullback.lift_snd _ _ _).symm
  have h₃ : ac ≫ rc = ra := canonicalPullbackDescentIso_reindex_hom_left_fst_fst
    q Z (Limits.pullback.lift a c (hab.trans hbc)) a c
      (Limits.pullback.lift_fst _ _ _).symm (Limits.pullback.lift_snd _ _ _).symm
  apply Iso.ext
  apply pullbackDescent_hom_ext q Z a c
  change (ab ≫ bc) ≫ rc = ac ≫ rc
  exact (Category.assoc ab bc rc).trans
    ((congrArg (fun k => ab ≫ k) h₂).trans (h₁.trans h₃.symm))

/-- The canonical native comparison restricts to the identity on the
actual diagonal. -/
theorem canonicalPullbackDescentIso_diagonal :
    reindexIso ((FiniteEtale.pullback q).obj Z) (canonicalPullbackDescentIso q Z)
        (Limits.pullback.diagonal q) (𝟙 Y) (𝟙 Y)
        (Limits.pullback.diagonal_fst q).symm (Limits.pullback.diagonal_snd q).symm =
      Iso.refl ((FiniteEtale.pullback (𝟙 Y)).obj ((FiniteEtale.pullback q).obj Z)) := by
  apply Iso.ext
  apply pullbackDescent_hom_ext q Z (𝟙 Y) (𝟙 Y)
  change _ = 𝟙 _ ≫ _
  rw [Category.id_comp]
  exact canonicalPullbackDescentIso_reindex_hom_left_fst_fst q Z
    (Limits.pullback.diagonal q) (𝟙 Y) (𝟙 Y)
    (Limits.pullback.diagonal_fst q).symm (Limits.pullback.diagonal_snd q).symm

/-- The identity comparison with a pulled-back cover respects its canonical
native overlap, over the original common composite. -/
theorem canonicalPullbackDescentIso_identity_overlap :
    ((MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) (Limits.pullback.fst q q) q).hom.app Z) ≫
        (FiniteEtale.pullback (Limits.pullback.fst q q)).map
          (𝟙 ((FiniteEtale.pullback q).obj Z)) ≫
        (canonicalPullbackDescentIso q Z).hom =
      ((MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) (Limits.pullback.snd q q) q
          (Limits.pullback.fst q q ≫ q) Limits.pullback.condition).hom.app Z) ≫
        (FiniteEtale.pullback (Limits.pullback.snd q q)).map
          (𝟙 ((FiniteEtale.pullback q).obj Z)) := by
  let W := (FiniteEtale.pullback q).obj Z
  let a : Limits.pullback q q ⟶ Y := Limits.pullback.fst q q
  let b : Limits.pullback q q ⟶ Y := Limits.pullback.snd q q
  let F : FiniteEtale Y ⥤ FiniteEtale (Limits.pullback q q) := FiniteEtale.pullback a
  let G : FiniteEtale Y ⥤ FiniteEtale (Limits.pullback q q) := FiniteEtale.pullback b
  let A : (FiniteEtale.pullback (a ≫ q)).obj Z ≅ F.obj W :=
    (MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤) a q).app Z
  let B : (FiniteEtale.pullback (a ≫ q)).obj Z ≅ G.obj W :=
    (MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤) b q (a ≫ q) Limits.pullback.condition).app Z
  change A.hom ≫ F.map (𝟙 W) ≫ (A.inv ≫ B.hom) = B.hom ≫ G.map (𝟙 W)
  calc
    _ = A.hom ≫ (𝟙 (F.obj W)) ≫ (A.inv ≫ B.hom) :=
      congrArg (fun k => A.hom ≫ k ≫ (A.inv ≫ B.hom)) (F.map_id W)
    _ = A.hom ≫ (A.inv ≫ B.hom) :=
      congrArg (fun k => A.hom ≫ k) (Category.id_comp (A.inv ≫ B.hom))
    _ = B.hom := (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ B.hom) A.hom_inv_id).trans (Category.id_comp B.hom))
    _ = B.hom ≫ (𝟙 (G.obj W)) := (Category.comp_id B.hom).symm
    _ = _ := congrArg (fun k => B.hom ≫ k) (G.map_id W).symm

end AlgebraicGeometry.FiniteEtale
