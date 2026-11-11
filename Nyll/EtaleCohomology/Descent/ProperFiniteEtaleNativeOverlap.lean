/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.ProperFiniteEtaleNativeDescent

/-!
# The original native overlap equation after proper descent

The sheaf overlap equation is faithful to the original finite étale
morphisms. Expressing both sides over the same composite map makes the
native pullback-pasting comparisons explicit, including their directions.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open EtaleFundamentalGroups.Cohomology

universe u

namespace EtaleCohomology.SetSheafDescent

attribute [local instance] FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

section CategoryCalculations

universe v w

variable {C : Type v} [Category.{w} C]

private theorem pasteComparison
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ : C}
    (γ : A₀ ⟶ A₁) (u : A₁ ⟶ A₆) (v : A₆ ⟶ A₇)
    (e : A₀ ⟶ A₂) (s : A₂ ⟶ A₃) (x : A₃ ⟶ A₄)
    (β : A₄ ⟶ A₆) (y : A₄ ⟶ A₅) (z : A₅ ⟶ A₇)
    (hγ : γ ≫ u = e ≫ s ≫ x ≫ β) (hβ : β ≫ v = y ≫ z) :
    γ ≫ (u ≫ v) = e ≫ s ≫ (x ≫ y) ≫ z := by
  calc
    _ = (γ ≫ u) ≫ v := (Category.assoc γ u v).symm
    _ = (e ≫ s ≫ x ≫ β) ≫ v := congrArg (fun k => k ≫ v) hγ
    _ = e ≫ s ≫ x ≫ (β ≫ v) := by simp only [Category.assoc]
    _ = e ≫ s ≫ x ≫ (y ≫ z) := congrArg (fun k => e ≫ s ≫ x ≫ k) hβ
    _ = _ := by simp only [Category.assoc]

private theorem pasteOverlap
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : C}
    (γ : A₀ ⟶ A₁) (u : A₁ ⟶ A₅) (v : A₅ ⟶ A₆)
    (s : A₀ ⟶ A₂) (x : A₂ ⟶ A₃) (β : A₃ ⟶ A₅)
    (y : A₃ ⟶ A₄) (z : A₄ ⟶ A₆)
    (hγ : γ ≫ u = s ≫ x ≫ β) (hβ : β ≫ v = y ≫ z) :
    γ ≫ (u ≫ v) = s ≫ (x ≫ y) ≫ z := by
  calc
    _ = (γ ≫ u) ≫ v := (Category.assoc γ u v).symm
    _ = (s ≫ x ≫ β) ≫ v := congrArg (fun k => k ≫ v) hγ
    _ = s ≫ x ≫ (β ≫ v) := by simp only [Category.assoc]
    _ = s ≫ x ≫ (y ≫ z) := congrArg (fun k => s ≫ x ≫ k) hβ
    _ = _ := by simp only [Category.assoc]

private theorem replaceOverlapPrefix
    {A₀ A₁ A₂ A₃ A₄ A₅ : C}
    (s : A₀ ⟶ A₁) (κ : A₁ ⟶ A₃) (e : A₀ ⟶ A₂) (t : A₂ ⟶ A₃)
    (r : A₃ ⟶ A₄) (z : A₄ ⟶ A₅) (h : s ≫ κ = e ≫ t) :
    e ≫ t ≫ r ≫ z = s ≫ (κ ≫ r) ≫ z := by
  calc
    _ = (e ≫ t) ≫ r ≫ z := by simp only [Category.assoc]
    _ = (s ≫ κ) ≫ r ≫ z := congrArg (fun k => k ≫ r ≫ z) h.symm
    _ = _ := by simp only [Category.assoc]

universe v₁ v₂ w₁ w₂

private theorem mapCompositionPasting
    {D : Type v₁} {E : Type v₂} [Category.{w₁} D] [Category.{w₂} E]
    (J : D ⥤ C) (H : E ⥤ C)
    {D₀ D₁ D₂ : D} {E₀ E₁ E₂ : E} {A B : C}
    (u : D₀ ⟶ D₁) (v : D₁ ⟶ D₂) (x : E₀ ⟶ E₁) (y : E₁ ⟶ E₂)
    (γ : A ⟶ J.obj D₀) (e : A ⟶ B) (s : B ⟶ H.obj E₀)
    (z : H.obj E₂ ⟶ J.obj D₂)
    (h : γ ≫ (J.map u ≫ J.map v) = e ≫ s ≫ (H.map x ≫ H.map y) ≫ z) :
    γ ≫ J.map (u ≫ v) = e ≫ s ≫ H.map (x ≫ y) ≫ z :=
  (congrArg (fun k => γ ≫ k) (J.map_comp u v)).trans
    (h.trans (congrArg (fun k => e ≫ s ≫ k ≫ z) (H.map_comp x y).symm))

private theorem overlapEquationIff
    {D : Type v₁} [Category.{w₁} D]
    (J : D ⥤ C) (FF : J.FullyFaithful)
    {D₀ D₁ D₂ D₃ D₄ : D} {C₀ C₁ C₂ C₃ C₄ C₅ : C}
    (A : D₀ ⟶ D₁) (ra : D₁ ⟶ D₂) (θ : D₂ ⟶ D₃)
    (B : D₀ ⟶ D₄) (rb : D₄ ⟶ D₃)
    (β : C₀ ≅ J.obj D₀) (Sa : C₀ ≅ C₁)
    (ca : C₂ ⟶ J.obj D₂) (cb : C₄ ≅ J.obj D₃)
    (E : C₀ ⟶ C₅) (Sb : C₅ ⟶ C₃) (κ : C₁ ⟶ C₃) (ψ : C₂ ⟶ C₄)
    (rA : C₁ ⟶ C₂) (rB : C₃ ⟶ C₄)
    (hA : β.hom ≫ J.map (A ≫ ra) = Sa.hom ≫ rA ≫ ca)
    (hB : β.hom ≫ J.map (B ≫ rb) = E ≫ Sb ≫ rB ≫ cb.hom)
    (hκ : Sa.hom ≫ κ = E ≫ Sb) (hθ : ca ≫ J.map θ = ψ ≫ cb.hom) :
    (rA ≫ ψ = κ ≫ rB) ↔ (A ≫ ra ≫ θ = B ≫ rb) := by
  have hm : J.map (A ≫ ra ≫ θ) = J.map (A ≫ ra) ≫ J.map θ :=
    (congrArg J.map (Category.assoc A ra θ).symm).trans (J.map_comp (A ≫ ra) θ)
  have hleft : β.hom ≫ J.map (A ≫ ra ≫ θ) =
      Sa.hom ≫ (rA ≫ ψ) ≫ cb.hom :=
    (congrArg (fun k => β.hom ≫ k) hm).trans
      (pasteOverlap β.hom (J.map (A ≫ ra)) (J.map θ)
        Sa.hom rA ca ψ cb.hom hA hθ)
  have hright : β.hom ≫ J.map (B ≫ rb) =
      Sa.hom ≫ (κ ≫ rB) ≫ cb.hom :=
    hB.trans (replaceOverlapPrefix Sa.hom κ E Sb rB cb.hom hκ)
  constructor
  · intro h
    apply FF.map_injective
    apply (cancel_epi β.hom).mp
    exact hleft.trans ((congrArg (fun k => Sa.hom ≫ k ≫ cb.hom) h).trans hright.symm)
  · intro h
    apply (cancel_mono cb.hom).mp
    apply (cancel_epi Sa.hom).mp
    exact hleft.symm.trans ((congrArg (fun k => β.hom ≫ J.map k) h).trans hright)

end CategoryCalculations

variable {X Y T : Scheme.{u}}

/-- Composition compatibility with a specified equal composite, using
exactly the existing native pullback-pasting comparison. -/
theorem finiteEtaleSheafPullbackIso_comp_hom_of_eq
    (a : T ⟶ Y) (q : Y ⟶ X) (g : T ⟶ X) (hg : g = a ≫ q)
    (V : FiniteEtale X) :
    ((finiteEtaleSheafPullbackIso g).app V).hom ≫
        (finiteEtaleSheaf T).map
          ((MorphismProperty.Over.pullbackComp
            (P := @IsFiniteEtale) (Q := ⊤) a q g hg).hom.app V) =
      (eqToIso (congrArg (fun f => etaleSetPullback f) hg)).hom.app
          ((finiteEtaleSheaf X).obj V) ≫
        (etaleSetPullbackCompIso a q).hom.app ((finiteEtaleSheaf X).obj V) ≫
          (etaleSetPullback a).map ((finiteEtaleSheafPullbackIso q).app V).hom ≫
            ((finiteEtaleSheafPullbackIso a).app ((FiniteEtale.pullback q).obj V)).hom := by
  cases hg
  exact (finiteEtaleSheafPullbackIso_comp_hom a q V).trans
    (Category.id_comp _).symm

/-- Pullback-pasting and a given native morphism transport to the
corresponding composite sheaf map, without changing its representer. -/
theorem finiteEtaleSheafPullbackIso_comp_map_hom
    (q : Y ⟶ X) (V : FiniteEtale X) (W : FiniteEtale Y)
    (ρ : (FiniteEtale.pullback q).obj V ⟶ W)
    (a : T ⟶ Y) (g : T ⟶ X) (hg : g = a ≫ q) :
    ((finiteEtaleSheafPullbackIso g).app V).hom ≫
        (finiteEtaleSheaf T).map
          (((MorphismProperty.Over.pullbackComp
            (P := @IsFiniteEtale) (Q := ⊤) a q g hg).hom.app V) ≫
              (FiniteEtale.pullback a).map ρ) =
      (eqToIso (congrArg (fun f => etaleSetPullback f) hg)).hom.app
          ((finiteEtaleSheaf X).obj V) ≫
        (etaleSetPullbackCompIso a q).hom.app ((finiteEtaleSheaf X).obj V) ≫
          (etaleSetPullback a).map
            (((finiteEtaleSheafPullbackIso q).app V).hom ≫
              (finiteEtaleSheaf Y).map ρ) ≫
            ((finiteEtaleSheafPullbackIso a).app W).hom := by
  cases hg
  let g : T ⟶ X := a ≫ q
  have hg : g = a ≫ q := rfl
  let J := finiteEtaleSheaf T
  let H := etaleSetPullback a
  let K := FiniteEtale.pullback a
  let F := (finiteEtaleSheaf X).obj V
  let C := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) a q g hg).app V
  let γ := (finiteEtaleSheafPullbackIso g).app V
  let E := (eqToIso (congrArg (fun f => etaleSetPullback f) hg)).app F
  let S := (etaleSetPullbackCompIso a q).app F
  let α := (finiteEtaleSheafPullbackIso q).app V
  let β := (finiteEtaleSheafPullbackIso a).app ((FiniteEtale.pullback q).obj V)
  let βW := (finiteEtaleSheafPullbackIso a).app W
  let r := (finiteEtaleSheaf Y).map ρ
  have hn : H.map r ≫ βW.hom = β.hom ≫ J.map (K.map ρ) :=
    (finiteEtaleSheafPullbackIso a).hom.naturality ρ
  have hc : γ.hom ≫ J.map C.hom =
      E.hom ≫ S.hom ≫ H.map α.hom ≫ β.hom :=
    finiteEtaleSheafPullbackIso_comp_hom_of_eq a q g hg V
  have hp := pasteComparison γ.hom (J.map C.hom) (J.map (K.map ρ))
    E.hom S.hom (H.map α.hom) β.hom (H.map r) βW.hom hc hn.symm
  change γ.hom ≫ J.map (C.hom ≫ K.map ρ) =
    E.hom ≫ S.hom ≫ H.map (α.hom ≫ r) ≫ βW.hom
  exact mapCompositionPasting J H C.hom (K.map ρ) α.hom r
    γ.hom E.hom S.hom βW.hom hp

/-- Component form of the original overlap cancellation, retaining the
specified equality between the two composites to the base. -/
theorem overlapComparison_hom_cancellation_app
    (q : Y ⟶ X) (F : Sheaf X.smallEtaleTopology (Type u)) :
    (etaleSetPullbackCompIso (pullback.fst q q) q).hom.app F ≫
        (overlapComparison q).hom.app F =
      (eqToIso (congrArg (fun f => etaleSetPullback f)
        (pullback.condition (f := q) (g := q)))).hom.app F ≫
          (etaleSetPullbackCompIso (pullback.snd q q) q).hom.app F :=
  CategoryTheory.congr_app (overlapComparison_hom_cancellation q) F

private theorem overlap_comp_map_fst
    (q : Y ⟶ X) (V : FiniteEtale X) (W : FiniteEtale Y)
    (ρ : (FiniteEtale.pullback q).obj V ⟶ W) :
    ((finiteEtaleSheafPullbackIso (pullback.fst q q ≫ q)).app V).hom ≫
        (finiteEtaleSheaf (pullback q q)).map
          (((MorphismProperty.Over.pullbackComp
            (P := @IsFiniteEtale) (Q := ⊤) (pullback.fst q q) q).hom.app V) ≫
              (FiniteEtale.pullback (pullback.fst q q)).map ρ) =
      (etaleSetPullbackCompIso (pullback.fst q q) q).hom.app
          ((finiteEtaleSheaf X).obj V) ≫
        (etaleSetPullback (pullback.fst q q)).map
          (((finiteEtaleSheafPullbackIso q).app V).hom ≫
            (finiteEtaleSheaf Y).map ρ) ≫
          ((finiteEtaleSheafPullbackIso (pullback.fst q q)).app W).hom := by
  have h := finiteEtaleSheafPullbackIso_comp_map_hom q V W ρ
    (pullback.fst q q) (pullback.fst q q ≫ q) rfl
  exact h.trans (Category.id_comp _)

private theorem overlap_comp_map_snd
    (q : Y ⟶ X) (V : FiniteEtale X) (W : FiniteEtale Y)
    (ρ : (FiniteEtale.pullback q).obj V ⟶ W) :
    ((finiteEtaleSheafPullbackIso (pullback.fst q q ≫ q)).app V).hom ≫
        (finiteEtaleSheaf (pullback q q)).map
          (((MorphismProperty.Over.pullbackComp
            (P := @IsFiniteEtale) (Q := ⊤) (pullback.snd q q) q
              (pullback.fst q q ≫ q) pullback.condition).hom.app V) ≫
                (FiniteEtale.pullback (pullback.snd q q)).map ρ) =
      (eqToIso (congrArg (fun f => etaleSetPullback f)
        (pullback.condition (f := q) (g := q)))).hom.app ((finiteEtaleSheaf X).obj V) ≫
        (etaleSetPullbackCompIso (pullback.snd q q) q).hom.app
            ((finiteEtaleSheaf X).obj V) ≫
          (etaleSetPullback (pullback.snd q q)).map
            (((finiteEtaleSheafPullbackIso q).app V).hom ≫
              (finiteEtaleSheaf Y).map ρ) ≫
            ((finiteEtaleSheafPullbackIso (pullback.snd q q)).app W).hom :=
  finiteEtaleSheafPullbackIso_comp_map_hom q V W ρ
    (pullback.snd q q) (pullback.fst q q ≫ q) pullback.condition

/-- The actual sheaf overlap equation is equivalent to its native
finite étale counterpart over the common composite to the base. -/
theorem sheaf_overlap_iff_native_overlap
    (q : Y ⟶ X) (V : FiniteEtale X) (W : FiniteEtale Y)
    (θ : (FiniteEtale.pullback (pullback.fst q q)).obj W ≅
      (FiniteEtale.pullback (pullback.snd q q)).obj W)
    (ρ : (FiniteEtale.pullback q).obj V ⟶ W) :
    (let r := ((finiteEtaleSheafPullbackIso q).app V).hom ≫ (finiteEtaleSheaf Y).map ρ
     (etaleSetPullback (pullback.fst q q)).map r ≫
         (finiteEtaleOverlapSheafIso W (pullback.fst q q) (pullback.snd q q) θ).hom =
       (overlapComparison q).hom.app ((finiteEtaleSheaf X).obj V) ≫
         (etaleSetPullback (pullback.snd q q)).map r) ↔
    ((MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) (pullback.fst q q) q).hom.app V) ≫
        (FiniteEtale.pullback (pullback.fst q q)).map ρ ≫ θ.hom =
      ((MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) (pullback.snd q q) q
          (pullback.fst q q ≫ q) pullback.condition).hom.app V) ≫
        (FiniteEtale.pullback (pullback.snd q q)).map ρ := by
  exact overlapEquationIff
    (C := Sheaf (pullback q q).smallEtaleTopology (Type u))
    (D := FiniteEtale (pullback q q))
    (finiteEtaleSheaf (pullback q q)) (finiteEtaleSheafFullyFaithful (pullback q q))
    (D₀ := (FiniteEtale.pullback (pullback.fst q q ≫ q)).obj V)
    (D₁ := (FiniteEtale.pullback (pullback.fst q q)).obj ((FiniteEtale.pullback q).obj V))
    (D₂ := (FiniteEtale.pullback (pullback.fst q q)).obj W)
    (D₃ := (FiniteEtale.pullback (pullback.snd q q)).obj W)
    (D₄ := (FiniteEtale.pullback (pullback.snd q q)).obj ((FiniteEtale.pullback q).obj V))
    (C₀ := (etaleSetPullback (pullback.fst q q ≫ q)).obj ((finiteEtaleSheaf X).obj V))
    (C₁ := (etaleSetPullback (pullback.fst q q)).obj
      ((etaleSetPullback q).obj ((finiteEtaleSheaf X).obj V)))
    (C₂ := (etaleSetPullback (pullback.fst q q)).obj ((finiteEtaleSheaf Y).obj W))
    (C₃ := (etaleSetPullback (pullback.snd q q)).obj
      ((etaleSetPullback q).obj ((finiteEtaleSheaf X).obj V)))
    (C₄ := (etaleSetPullback (pullback.snd q q)).obj ((finiteEtaleSheaf Y).obj W))
    (C₅ := (etaleSetPullback (pullback.snd q q ≫ q)).obj ((finiteEtaleSheaf X).obj V))
    ((MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤) (pullback.fst q q) q).hom.app V)
    ((FiniteEtale.pullback (pullback.fst q q)).map ρ) θ.hom
    ((MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤) (pullback.snd q q) q
        (pullback.fst q q ≫ q) pullback.condition).hom.app V)
    ((FiniteEtale.pullback (pullback.snd q q)).map ρ)
    ((finiteEtaleSheafPullbackIso (pullback.fst q q ≫ q)).app V)
    ((etaleSetPullbackCompIso (pullback.fst q q) q).app ((finiteEtaleSheaf X).obj V))
    ((finiteEtaleSheafPullbackIso (pullback.fst q q)).app W).hom
    ((finiteEtaleSheafPullbackIso (pullback.snd q q)).app W)
    ((eqToIso (congrArg (fun f => etaleSetPullback f)
      (pullback.condition (f := q) (g := q)))).hom.app ((finiteEtaleSheaf X).obj V))
    ((etaleSetPullbackCompIso (pullback.snd q q) q).hom.app ((finiteEtaleSheaf X).obj V))
    ((overlapComparison q).hom.app ((finiteEtaleSheaf X).obj V))
    (finiteEtaleOverlapSheafIso W (pullback.fst q q) (pullback.snd q q) θ).hom
    ((etaleSetPullback (pullback.fst q q)).map
      (((finiteEtaleSheafPullbackIso q).app V).hom ≫ (finiteEtaleSheaf Y).map ρ))
    ((etaleSetPullback (pullback.snd q q)).map
      (((finiteEtaleSheafPullbackIso q).app V).hom ≫ (finiteEtaleSheaf Y).map ρ))
    (overlap_comp_map_fst q V W ρ) (overlap_comp_map_snd q V W ρ)
    (overlapComparison_hom_cancellation_app q ((finiteEtaleSheaf X).obj V))
    (finiteEtaleOverlapSheafIso_square W (pullback.fst q q) (pullback.snd q q) θ)

/-- The sheaf compatibility of a recovered cover implies the literal
native overlap equation over the common composite to the base. -/
theorem native_overlap_of_sheaf_overlap
    (q : Y ⟶ X) (V : FiniteEtale X) (W : FiniteEtale Y)
    (θ : (FiniteEtale.pullback (pullback.fst q q)).obj W ≅
      (FiniteEtale.pullback (pullback.snd q q)).obj W)
    (ρ : (FiniteEtale.pullback q).obj V ⟶ W)
    (hρ :
      let r := ((finiteEtaleSheafPullbackIso q).app V).hom ≫ (finiteEtaleSheaf Y).map ρ
      (etaleSetPullback (pullback.fst q q)).map r ≫
          (finiteEtaleOverlapSheafIso W (pullback.fst q q) (pullback.snd q q) θ).hom =
        (overlapComparison q).hom.app ((finiteEtaleSheaf X).obj V) ≫
          (etaleSetPullback (pullback.snd q q)).map r) :
    ((MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) (pullback.fst q q) q).hom.app V) ≫
        (FiniteEtale.pullback (pullback.fst q q)).map ρ ≫ θ.hom =
      ((MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) (pullback.snd q q) q
          (pullback.fst q q ≫ q) pullback.condition).hom.app V) ≫
        (FiniteEtale.pullback (pullback.snd q q)).map ρ :=
  (sheaf_overlap_iff_native_overlap q V W θ ρ).mp hρ

/-- Native overlap compatibility gives the actual represented-sheaf
compatibility, retaining the original cover comparison. -/
theorem sheaf_overlap_of_native_overlap
    (q : Y ⟶ X) (V : FiniteEtale X) (W : FiniteEtale Y)
    (θ : (FiniteEtale.pullback (pullback.fst q q)).obj W ≅
      (FiniteEtale.pullback (pullback.snd q q)).obj W)
    (ρ : (FiniteEtale.pullback q).obj V ⟶ W)
    (hρ :
      ((MorphismProperty.Over.pullbackComp
          (P := @IsFiniteEtale) (Q := ⊤) (pullback.fst q q) q).hom.app V) ≫
          (FiniteEtale.pullback (pullback.fst q q)).map ρ ≫ θ.hom =
        ((MorphismProperty.Over.pullbackComp
          (P := @IsFiniteEtale) (Q := ⊤) (pullback.snd q q) q
            (pullback.fst q q ≫ q) pullback.condition).hom.app V) ≫
          (FiniteEtale.pullback (pullback.snd q q)).map ρ) :
    let r := ((finiteEtaleSheafPullbackIso q).app V).hom ≫ (finiteEtaleSheaf Y).map ρ
    (etaleSetPullback (pullback.fst q q)).map r ≫
        (finiteEtaleOverlapSheafIso W (pullback.fst q q) (pullback.snd q q) θ).hom =
      (overlapComparison q).hom.app ((finiteEtaleSheaf X).obj V) ≫
        (etaleSetPullback (pullback.snd q q)).map r :=
  (sheaf_overlap_iff_native_overlap q V W θ ρ).mpr hρ

end EtaleCohomology.SetSheafDescent
