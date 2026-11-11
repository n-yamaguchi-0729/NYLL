/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Etale.ProperFiberIsomorphismNeighborhood
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Spreading invertibility of the actual finite étale pullback map

The native finite étale pullback functor gives a cartesian square on every
morphism. Its original map on a specified base change therefore supplies the
input to the existing proper isomorphism-neighborhood theorem. The resulting
neighborhood makes the same native finite étale map invertible.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteEtale

/-- The actual map of the finite étale inverse-image functor is cartesian
over the original morphism. -/
theorem isPullback_pullback_map
    {Y T : Scheme.{u}} (r : T ⟶ Y) {V W : FiniteEtale Y} (m : V ⟶ W) :
    IsPullback ((FiniteEtale.pullback r).map m).hom.left
      (Limits.pullback.fst V.hom r) (Limits.pullback.fst W.hom r) m.hom.left := by
  have hm₁ : ((FiniteEtale.pullback r).map m).hom.left ≫
      Limits.pullback.fst W.hom r =
        Limits.pullback.fst V.hom r ≫ m.hom.left :=
    Limits.pullback.lift_fst _ _ _
  have hm₂ : ((FiniteEtale.pullback r).map m).hom.left ≫
      Limits.pullback.snd W.hom r = Limits.pullback.snd V.hom r :=
    Limits.pullback.lift_snd _ _ _
  have houter : IsPullback
      (((FiniteEtale.pullback r).map m).hom.left ≫ Limits.pullback.snd W.hom r)
      (Limits.pullback.fst V.hom r) r (m.hom.left ≫ W.hom) := by
    have hw : m.hom.left ≫ W.hom = V.hom := m.hom.w
    rw [hm₂]
    exact hw.symm ▸ (IsPullback.of_hasPullback V.hom r).flip
  exact houter.of_right hm₁ (IsPullback.of_hasPullback W.hom r).flip

/-- An isomorphism after the specified original base change spreads over
the entire inverse image of an open neighborhood in the base. -/
theorem exists_isIso_pullback_open_of_isIso_pullback
    {X Y T : Scheme.{u}} (q : Y ⟶ X) [UniversallyClosed q] (t : T ⟶ X)
    {V W : FiniteEtale Y} (m : V ⟶ W)
    [IsIso ((FiniteEtale.pullback (Limits.pullback.fst q t)).map m)]
    (a : T) :
    ∃ U : X.Opens, t a ∈ U ∧
      IsIso ((FiniteEtale.pullback (q ⁻¹ᵁ U).ι).map m) := by
  let r : Limits.pullback q t ⟶ Y := Limits.pullback.fst q t
  let m₀ : Limits.pullback V.hom r ⟶ Limits.pullback W.hom r :=
    ((FiniteEtale.pullback r).map m).hom.left
  have hm₀ : IsIso m₀ := by
    exact inferInstanceAs
      (IsIso ((FiniteEtale.forget _ ⋙ Over.forget _).map
        ((FiniteEtale.pullback (Limits.pullback.fst q t)).map m)))
  have hw := (IsPullback.of_hasPullback W.hom r).paste_vert
    (IsPullback.of_hasPullback q t)
  let e : Limits.pullback W.hom r ≅ Limits.pullback (W.hom ≫ q) t :=
    hw.isoPullback
  have he : e.hom ≫ Limits.pullback.fst (W.hom ≫ q) t =
      Limits.pullback.fst W.hom r := hw.isoPullback_hom_fst
  have hcart : IsPullback (Limits.pullback.fst V.hom r) (m₀ ≫ e.hom)
      m.hom.left (Limits.pullback.fst (W.hom ≫ q) t) := by
    apply (isPullback_pullback_map r m).flip.of_iso
      (Iso.refl _) (Iso.refl _) e (Iso.refl _)
    · exact (Category.comp_id (Limits.pullback.fst V.hom r)).trans
        (Category.id_comp (Limits.pullback.fst V.hom r)).symm
    · exact (Category.id_comp (m₀ ≫ e.hom)).symm
    · exact (Category.comp_id m.hom.left).trans (Category.id_comp m.hom.left).symm
    · exact (Category.comp_id (Limits.pullback.fst W.hom r)).trans he.symm
  have hcanon : IsIso
      (Limits.pullback.snd m.hom.left (Limits.pullback.fst (W.hom ≫ q) t)) := by
    rw [← hcart.isoPullback_inv_snd]
    infer_instance
  have hproperW : UniversallyClosed (W.hom ≫ q) := inferInstance
  obtain ⟨U, ha, hU⟩ :=
    m.hom.left.exists_isIso_restrict_preimage_of_isIso_baseChange (W.hom ≫ q) t a
  refine ⟨U, ha, ?_⟩
  let B : Y.Opens := q ⁻¹ᵁ U
  let D : W.left.Opens := (W.hom ≫ q) ⁻¹ᵁ U
  let mU := (FiniteEtale.pullback B.ι).map m
  have hU' : IsIso (m.hom.left ∣_ D) := hU
  have hmU : IsIso mU.hom.left := by
    apply (Scheme.Hom.isIso_iff_finrank_eq mU.hom.left).mpr
    funext w
    have hwB : W.hom (Limits.pullback.fst W.hom B.ι w) ∈ B := by
      have heq := congrArg (fun k : Limits.pullback W.hom B.ι ⟶ Y => k w)
        (Limits.pullback.condition (f := W.hom) (g := B.ι))
      change W.hom (Limits.pullback.fst W.hom B.ι w) =
        B.ι (Limits.pullback.snd W.hom B.ι w) at heq
      rw [heq]
      exact (Limits.pullback.snd W.hom B.ι w).property
    let wD : D := ⟨Limits.pullback.fst W.hom B.ι w, hwB⟩
    calc
      mU.hom.left.finrank w =
          m.hom.left.finrank (Limits.pullback.fst W.hom B.ι w) :=
        Scheme.Hom.finrank_of_isPullback _ _ _ _
          (isPullback_pullback_map B.ι m).flip w
      _ = (m.hom.left ∣_ D).finrank wD :=
        (Scheme.Hom.finrank_of_isPullback _ _ _ _
          (isPullback_morphismRestrict m.hom.left D).flip wD).symm
      _ = 1 := congrFun (Scheme.Hom.finrank_eq_one_of_isIso (m.hom.left ∣_ D)) wD
  have : IsIso ((FiniteEtale.forget _ ⋙ Over.forget _).map mU) := hmU
  exact isIso_of_reflects_iso mU (FiniteEtale.forget _ ⋙ Over.forget _)

end AlgebraicGeometry.FiniteEtale
