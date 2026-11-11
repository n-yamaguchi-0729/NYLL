/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.ProperFiniteEtaleIsoDescent
public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperClosedFiberDescentRecovery
public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperCompleteProjectiveCoverLift
public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperHenselianFullyFaithful
public import Nyll.EtaleFundamentalGroups.FiniteEtale.HenselianAscent
public import Mathlib.CategoryTheory.Equivalence

/-!
# Proper finite étale comparison over a complete Noetherian local base

The actual finite projective cover supplies a native finite étale descent
datum. Proper effective descent produces a cover on the original proper
scheme. Descent of the original closed-fiber isomorphism recovers the given
closed-fiber cover. Combining this construction with proper henselian full
faithfulness yields the equivalence whose forward functor is literally the
original closed-fiber pullback.

The proper morphism need not be flat. The base is complete Noetherian local;
the arbitrary henselian-local essential-surjectivity theorem is separate.
Reference: the complete-local case of Stacks Project, Lemma 58.9.1 (0A48).
https://stacks.math.columbia.edu/tag/0A48
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits
open EtaleCohomology.SetSheafDescent

namespace AlgebraicGeometry.FiniteEtale

open ProperHenselianActionLifting

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

/-- Descend an actual finite étale cover and recover its prescribed
restriction by descending the original comparison under the base-changed
proper surjection. -/
theorem exists_finiteEtale_lift_of_proper_cover_descent
    {X X₀ Y : Scheme.{u}} (i : X₀ ⟶ X) (q : Y ⟶ X)
    [IsProper q] [Surjective q] (W : FiniteEtale Y) (V : FiniteEtale X₀)
    (e : (FiniteEtale.pullback (pullback.fst q i)).obj W ≅
      (FiniteEtale.pullback (pullback.snd q i)).obj V)
    (θ : (FiniteEtale.pullback (pullback.fst q q)).obj W ≅
      (FiniteEtale.pullback (pullback.snd q q)).obj W)
    (htriple :
      finiteEtalePairIso q W θ (radicialTripleFirst q)
          (radicialTripleSecond q) (radicialTriple_first_second q) ≪≫
        finiteEtalePairIso q W θ (radicialTripleSecond q)
          (radicialTripleThird q) (radicialTriple_second_third q) =
      finiteEtalePairIso q W θ (radicialTripleFirst q)
        (radicialTripleThird q) (radicialTriple_first_third q))
    (hθ :
      (FiniteEtale.pullback (pullback.fst (pullback.fst q q ≫ q) i)).map θ.hom =
        (restrictionIso i q (pullback.fst q q ≫ q) W V e
          (pullback.fst q q) rfl).hom ≫
          (restrictionIso i q (pullback.fst q q ≫ q) W V e
            (pullback.snd q q) pullback.condition.symm).inv) :
    ∃ Z : FiniteEtale X, Nonempty ((FiniteEtale.pullback i).obj Z ≅ V) := by
  obtain ⟨Z, _eZ, ρ, _hcounit, hρ⟩ :=
    exists_finiteEtale_descent_of_proper_surjective_native q W θ htriple
  let a : Limits.pullback q q ⟶ Y := pullback.fst q q
  let b : Limits.pullback q q ⟶ Y := pullback.snd q q
  let F : FiniteEtale Y ⥤ FiniteEtale (Limits.pullback q q) := FiniteEtale.pullback a
  let G : FiniteEtale Y ⥤ FiniteEtale (Limits.pullback q q) := FiniteEtale.pullback b
  let U := (FiniteEtale.pullback q).obj Z
  let T := (FiniteEtale.pullback (a ≫ q)).obj Z
  let A : T ≅ F.obj U := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) a q).app Z
  let B : T ≅ G.obj U := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) b q (a ≫ q) pullback.condition).app Z
  have hρnative : A.hom ≫ F.map ρ.hom ≫ θ.hom = B.hom ≫ G.map ρ.hom :=
    native_overlap_of_sheaf_overlap q Z W θ ρ.hom hρ
  have hcancel : A.hom ≫ ((A.inv ≫ B.hom) ≫ G.map ρ.hom) =
      B.hom ≫ G.map ρ.hom :=
    (congrArg (fun k => A.hom ≫ k) (Category.assoc A.inv B.hom (G.map ρ.hom))).trans
      (A.hom_inv_id_assoc (B.hom ≫ G.map ρ.hom))
  have hρcanonical : F.map ρ.hom ≫ θ.hom =
      (canonicalPullbackDescentIso q Z).hom ≫ G.map ρ.hom :=
    (cancel_epi A.hom).mp (hρnative.trans hcancel.symm)
  let g : Limits.pullback q q ⟶ X := a ≫ q
  let H : FiniteEtale (Limits.pullback q q) ⥤ FiniteEtale (Limits.pullback g i) :=
    FiniteEtale.pullback (pullback.fst g i)
  let Q : FiniteEtale X₀ ⥤ FiniteEtale (Limits.pullback g i) :=
    FiniteEtale.pullback (pullback.snd g i)
  let e₁ : H.obj (F.obj W) ≅ Q.obj V := restrictionIso i q g W V e a rfl
  let e₂ : H.obj (G.obj W) ≅ Q.obj V :=
    restrictionIso i q g W V e b pullback.condition.symm
  have heq : H.map θ.hom = e₁.hom ≫ e₂.inv := hθ
  have hθ' : H.map θ.hom ≫ e₂.hom = e₁.hom :=
    (congrArg (fun k => k ≫ e₂.hom) heq).trans
      ((Category.assoc e₁.hom e₂.inv e₂.hom).trans
        ((congrArg (fun k => e₁.hom ≫ k) e₂.inv_hom_id).trans (Category.comp_id _)))
  let q₀ : Limits.pullback q i ⟶ X₀ := pullback.snd q i
  let Z₀ : FiniteEtale X₀ := (FiniteEtale.pullback i).obj Z
  let ρ₀ : (FiniteEtale.pullback q₀).obj Z₀ ≅ (FiniteEtale.pullback q₀).obj V :=
    closedFiberRecoveryIso i q Z W V ρ e
  let a₀ : Limits.pullback q₀ q₀ ⟶ Limits.pullback q i := pullback.fst q₀ q₀
  let b₀ : Limits.pullback q₀ q₀ ⟶ Limits.pullback q i := pullback.snd q₀ q₀
  let F₀ : FiniteEtale (Limits.pullback q i) ⥤ FiniteEtale (Limits.pullback q₀ q₀) :=
    FiniteEtale.pullback a₀
  let G₀ : FiniteEtale (Limits.pullback q i) ⥤ FiniteEtale (Limits.pullback q₀ q₀) :=
    FiniteEtale.pullback b₀
  let U₀ := (FiniteEtale.pullback q₀).obj Z₀
  let T₀ := (FiniteEtale.pullback (a₀ ≫ q₀)).obj Z₀
  let A₀ : T₀ ≅ F₀.obj U₀ := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) a₀ q₀).app Z₀
  let B₀ : T₀ ≅ G₀.obj U₀ := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) b₀ q₀ (a₀ ≫ q₀) pullback.condition).app Z₀
  let θ₀ := canonicalPullbackDescentIso q₀ V
  have hrec : F₀.map ρ₀.hom ≫ θ₀.hom = (A₀.inv ≫ B₀.hom) ≫ G₀.map ρ₀.hom :=
    closedFiberRecoveryIso_overlap i q Z W V ρ e θ hρcanonical hθ'
  have hrecnative : A₀.hom ≫ F₀.map ρ₀.hom ≫ θ₀.hom = B₀.hom ≫ G₀.map ρ₀.hom :=
    (congrArg (fun k => A₀.hom ≫ k) hrec).trans
      ((congrArg (fun k => A₀.hom ≫ k)
        (Category.assoc A₀.inv B₀.hom (G₀.map ρ₀.hom))).trans
          (A₀.hom_inv_id_assoc (B₀.hom ≫ G₀.map ρ₀.hom)))
  obtain ⟨τ, _hτ, _huniq⟩ := existsUnique_iso_of_proper_pullback q₀ Z₀ V ρ₀ hrecnative
  exact ⟨Z, ⟨τ⟩⟩

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]

/-- Every finite étale cover of the original closed fiber lifts to the
original proper scheme over a complete Noetherian local base. No flatness
of the proper family is assumed. -/
theorem exists_proper_finiteEtale_lift_of_isAdicComplete
    (V : FiniteEtale (Limits.pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))) :
    ∃ Z : FiniteEtale X,
      Nonempty ((FiniteEtale.pullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).obj Z ≅ V) := by
  obtain ⟨m, Y, _d, q, _j, _hj, hproper, hsurj, W, e, θ, hdata⟩ :=
    exists_proper_projective_cover_descent_data R f V
  let p : (∐ Y) ⟶ X := Sigma.desc q
  have : IsProper p := hproper
  have : Surjective p := hsurj
  exact exists_finiteEtale_lift_of_proper_cover_descent
    (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) p
    W V e θ hdata.2.1 hdata.1

/-- The canonical closed-fiber pullback is essentially surjective for
an arbitrary proper scheme over a complete Noetherian local ring. -/
theorem pullback_essSurj_closedFiber_of_isProper_of_isAdicComplete :
    (FiniteEtale.pullback
      (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).EssSurj where
  mem_essImage V := exists_proper_finiteEtale_lift_of_isAdicComplete R f V

/-- The literal closed-fiber pullback is an equivalence over a complete
Noetherian local base: actual lifting supplies essential surjectivity,
and proper henselian full faithfulness supplies the other two properties. -/
theorem pullback_isEquivalence_closedFiber_of_isProper_of_isAdicComplete :
    (FiniteEtale.pullback
      (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).IsEquivalence := by
  have : HenselianLocalRing R :=
    EtaleFundamentalGroups.henselianLocalRing_of_finiteEtale_local_of_isAdicComplete
      (R := R) (S := R)
  let FF := pullbackFullyFaithful_closedFiber_of_isProper_of_henselianLocalRing f
  exact
    { faithful := FF.faithful
      full := FF.full
      essSurj := pullback_essSurj_closedFiber_of_isProper_of_isAdicComplete R f }

/-- The comparison equivalence uses the original closed-fiber pullback
as its forward functor. -/
def properCompleteFiniteEtaleEquivalence :
    FiniteEtale X ≌
      FiniteEtale (Limits.pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) := by
  have : (FiniteEtale.pullback
      (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).IsEquivalence :=
    pullback_isEquivalence_closedFiber_of_isProper_of_isAdicComplete R f
  exact (FiniteEtale.pullback
    (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).asEquivalence

end AlgebraicGeometry.FiniteEtale
