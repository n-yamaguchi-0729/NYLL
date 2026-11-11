/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicClosedProjectiveFiniteEtale
public import Nyll.EtaleFundamentalGroups.FiniteEtale.HenselianAscent
public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperHenselianActionPullback
public import Nyll.SchemeTheory.Morphisms.ProperFiniteProjectiveCover
public import Nyll.SchemeTheory.Morphisms.SigmaPullback
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.VanKampen
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# A finite étale lift on an actual proper projective cover

The finite projective cover of the original proper family supplies the
component schemes. The complete-local algebraization theorem lifts the
original closed-fiber cover on each component. Existing finite-coproduct
and universal-colimit results assemble the lifts and their specified
closed-fiber comparisons on the actual coproduct cover.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale.ProperHenselianActionLifting

attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

private theorem exists_sigma_comparison
    {X X₀ : Scheme.{u}} (i : X₀ ⟶ X) (m : ℕ) (Y : Fin m → Scheme.{u})
    (q : ∀ j, Y j ⟶ X) (V : FiniteEtale X₀)
    (W : ∀ j, FiniteEtale (Y j))
    (e : ∀ j, (FiniteEtale.pullback (Limits.pullback.fst (q j) i)).obj (W j) ≅
      (FiniteEtale.pullback (Limits.pullback.snd (q j) i)).obj V) :
    ∃ WSum : FiniteEtale (∐ Y),
      Nonempty ((FiniteEtale.pullback (Limits.pullback.fst (Sigma.desc q) i)).obj WSum ≅
        (FiniteEtale.pullback (Limits.pullback.snd (Sigma.desc q) i)).obj V) := by
  let A : Fin m → Scheme.{u} := fun j => (W j).left
  let w : ∀ j, A j ⟶ Y j := fun j => (W j).hom
  let B : Fin m → Scheme.{u} := fun j => Limits.pullback (q j) i
  let bY : ∀ j, B j ⟶ Y j := fun j => Limits.pullback.fst (q j) i
  let bX : ∀ j, B j ⟶ X₀ := fun j => Limits.pullback.snd (q j) i
  let C : Fin m → Scheme.{u} := fun j => Limits.pullback (w j) (bY j)
  let cA : ∀ j, C j ⟶ A j := fun j => Limits.pullback.fst (w j) (bY j)
  let cB : ∀ j, C j ⟶ B j := fun j => Limits.pullback.snd (w j) (bY j)
  let v : V.left ⟶ X₀ := V.hom
  let E (j : Fin m) : C j ≅ Limits.pullback v (bX j) :=
    (FiniteEtale.forget (B j) ⋙ Over.forget (B j)).mapIso (e j)
  let cV : ∀ j, C j ⟶ V.left :=
    fun j => (E j).hom ≫ Limits.pullback.fst v (bX j)
  have hEsnd (j : Fin m) :
      (E j).hom ≫ Limits.pullback.snd v (bX j) = cB j :=
    MorphismProperty.Over.w (e j).hom
  have hCV (j : Fin m) : IsPullback (cV j) (cB j) v (bX j) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ (E j) rfl (hEsnd j)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => (E j).hom ≫ k) Limits.pullback.condition).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ bX j) (hEsnd j))))
  let hB := coproductIsCoproduct B
  let hC := coproductIsCoproduct C
  let yY : ∐ B ⟶ ∐ Y := Cofan.IsColimit.desc hB (fun j => bY j ≫ Sigma.ι Y j)
  let yX : ∐ B ⟶ X₀ := Cofan.IsColimit.desc hB bX
  let zA : ∐ C ⟶ ∐ A := Cofan.IsColimit.desc hC (fun j => cA j ≫ Sigma.ι A j)
  let zB : ∐ C ⟶ ∐ B := Cofan.IsColimit.desc hC (fun j => cB j ≫ Sigma.ι B j)
  let zX : ∐ C ⟶ X₀ := Cofan.IsColimit.desc hC (fun j => cB j ≫ bX j)
  let zV : ∐ C ⟶ V.left := Cofan.IsColimit.desc hC cV
  let wSum : ∐ A ⟶ ∐ Y := Limits.Sigma.map w
  have hw : ∀ j, IsFiniteEtale (w j) := fun j => inferInstanceAs (IsFiniteEtale (W j).hom)
  have hwSum : IsFiniteEtale wSum := IsFiniteEtale.sigmaMap w
  have hY : IsPullback yY yX (Sigma.desc q) i :=
    IsUniversalColimit.isPullback_of_isColimit_right (X := Y) (P := B)
      (FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct Y))
      q (Sigma.desc q) i bY bX
      (fun j => IsPullback.of_hasPullback (q j) i) hB
      (fun j => Sigma.ι_comp_desc q j)
  have hA : IsPullback zA zX (Sigma.desc (fun j => w j ≫ q j)) i :=
    IsUniversalColimit.isPullback_of_isColimit_right (X := A) (P := C)
      (FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct A))
      (fun j => w j ≫ q j) (Sigma.desc (fun j => w j ≫ q j)) i
      cA (fun j => cB j ≫ bX j)
      (fun j => (IsPullback.of_hasPullback (w j) (bY j)).paste_vert
        (IsPullback.of_hasPullback (q j) i)) hC
      (fun j => Sigma.ι_comp_desc (fun j => w j ≫ q j) j)
  have hV : IsPullback zB zV yX v :=
    IsUniversalColimit.isPullback_of_isColimit_right (X := B) (P := C)
      (FinitaryPreExtensive.isUniversal_finiteCoproducts hB)
      bX yX v cB cV (fun j => (hCV j).flip) hC
      (fun j => Cofan.IsColimit.fac hB bX j)
  have hZX : zB ≫ yX = zX := by
    apply Cofan.IsColimit.hom_ext hC
    intro j
    simp only [zB, yX, zX, Category.assoc, Cofan.IsColimit.fac_assoc,
      Cofan.IsColimit.fac]
    exact congrArg (fun k => cB j ≫ k) (Cofan.IsColimit.fac hB bX j)
  have hwq : wSum ≫ Sigma.desc q = Sigma.desc (fun j => w j ≫ q j) := by
    apply Sigma.hom_ext
    intro j
    change Sigma.ι A j ≫ (Limits.Sigma.map w ≫ Sigma.desc q) =
      Sigma.ι A j ≫ Sigma.desc (fun j => w j ≫ q j)
    rw [← Category.assoc, Sigma.ι_map, Category.assoc,
      Sigma.ι_comp_desc, Sigma.ι_comp_desc]
  have hsquare : zA ≫ wSum = zB ≫ yY := by
    apply Cofan.IsColimit.hom_ext hC
    intro j
    simp only [zA, zB, yY, wSum, Category.assoc, Cofan.IsColimit.fac_assoc,
      Sigma.ι_map]
    have hyY : Sigma.ι B j ≫ yY = bY j ≫ Sigma.ι Y j :=
      Cofan.IsColimit.fac hB (fun j => bY j ≫ Sigma.ι Y j) j
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ Sigma.ι Y j) Limits.pullback.condition).trans
        ((Category.assoc _ _ _).trans (congrArg (fun k => cB j ≫ k) hyY.symm)))
  have hA' : IsPullback zA zB wSum yY := by
    have h := hA
    rw [← hwq, ← hZX] at h
    exact h.of_bot hsquare hY
  let β : ∐ B ≅ Limits.pullback (Sigma.desc q) i := hY.isoPullback
  have hA'' : IsPullback zA (zB ≫ β.hom) wSum
      (Limits.pullback.fst (Sigma.desc q) i) :=
    hA'.of_iso (Iso.refl _) (Iso.refl _) β (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by simp only [Iso.refl_hom, Category.id_comp])
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      ((Category.comp_id _).trans hY.isoPullback_hom_fst.symm)
  have hV' : IsPullback zV (zB ≫ β.hom) v
      (Limits.pullback.snd (Sigma.desc q) i) :=
    hV.flip.of_iso (Iso.refl _) (Iso.refl _) β (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by simp only [Iso.refl_hom, Category.id_comp])
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      ((Category.comp_id _).trans hY.isoPullback_hom_snd.symm)
  let eSum := hA''.isoPullback.symm ≪≫ hV'.isoPullback
  have heSum : eSum.hom ≫ Limits.pullback.snd v (Limits.pullback.snd (Sigma.desc q) i) =
      Limits.pullback.snd wSum (Limits.pullback.fst (Sigma.desc q) i) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => hA''.isoPullback.inv ≫ k) hV'.isoPullback_hom_snd).trans
        hA''.isoPullback_inv_snd)
  exact ⟨FiniteEtale.mk wSum, ⟨MorphismProperty.Over.isoMk eSum heSum⟩⟩

private theorem closedProjective_component_essSurj
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (q : Y ⟶ X) (n : ℕ)
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsClosedImmersion j] (hj : j ≫ ProjSpace.π R n = q ≫ f) :
    let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let i := Limits.pullback.fst f r
    (FiniteEtale.pullback (Limits.pullback.fst q i)).EssSurj := by
  intro r i
  have hJ := pullback_essSurj_closedProjective_of_isAdicComplete R n j
  have hF : (FiniteEtale.pullback (Limits.pullback.fst (q ≫ f) r)).EssSurj := by
    rw [← hj]
    exact hJ
  let h := (IsPullback.of_hasPullback q i).paste_vert (IsPullback.of_hasPullback f r)
  let c : Limits.pullback q i ≅ Limits.pullback (q ≫ f) r := h.isoPullback
  let E : FiniteEtale (Limits.pullback (q ≫ f) r) ≌
      FiniteEtale (Limits.pullback q i) :=
    MorphismProperty.Over.pullbackIso
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ c.symm
  have hE : (FiniteEtale.pullback c.hom).IsEquivalence := E.isEquivalence_functor
  let e : FiniteEtale.pullback (Limits.pullback.fst q i) ≅
      FiniteEtale.pullback (Limits.pullback.fst (q ≫ f) r) ⋙
        FiniteEtale.pullback c.hom :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      c.hom (Limits.pullback.fst (q ≫ f) r) (Limits.pullback.fst q i)
      h.isoPullback_hom_fst.symm
  exact Functor.essSurj_of_iso e.symm

/-- The original closed-fiber cover supplies an actual finite étale
cover on a finite proper projective cover of the original family. Its
specified closed-fiber comparison gives an overlap isomorphism with
the original restriction formula, triple cocycle and diagonal identity. -/
theorem exists_proper_projective_cover_descent_data
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] :
    let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let X₀ : Scheme.{u} := Limits.pullback f r
    let i : X₀ ⟶ X := Limits.pullback.fst f r
    ∀ V : FiniteEtale X₀,
      ∃ (m : ℕ) (Y : Fin m → Scheme.{u}) (d : Fin m → ℕ)
        (q : ∀ k, Y k ⟶ X)
        (j : ∀ k, Y k ⟶
          Proj (MvPolynomial.homogeneousSubmodule (Fin (d k + 1)) R)),
        (∀ k, IsIntegral (Y k) ∧ IsProper (q k) ∧ IsClosedImmersion (j k) ∧
          j k ≫ ProjSpace.π R (d k) = q k ≫ f) ∧
        IsProper (Sigma.desc q) ∧ Surjective (Sigma.desc q) ∧
        ∃ W : FiniteEtale (∐ Y),
        ∃ e : (FiniteEtale.pullback (Limits.pullback.fst (Sigma.desc q) i)).obj W ≅
            (FiniteEtale.pullback (Limits.pullback.snd (Sigma.desc q) i)).obj V,
        ∃ θ : (FiniteEtale.pullback
            (Limits.pullback.fst (Sigma.desc q) (Sigma.desc q))).obj W ≅
          (FiniteEtale.pullback
            (Limits.pullback.snd (Sigma.desc q) (Sigma.desc q))).obj W,
          let g := Limits.pullback.fst (Sigma.desc q) (Sigma.desc q) ≫ Sigma.desc q
          let e₁ := restrictionIso i (Sigma.desc q) g W V e
            (Limits.pullback.fst (Sigma.desc q) (Sigma.desc q)) rfl
          let e₂ := restrictionIso i (Sigma.desc q) g W V e
            (Limits.pullback.snd (Sigma.desc q) (Sigma.desc q))
            Limits.pullback.condition.symm
          (FiniteEtale.pullback (Limits.pullback.fst g i)).map θ.hom =
              e₁.hom ≫ e₂.inv ∧
          (let a := radicialTripleFirst (Sigma.desc q)
           let b := radicialTripleSecond (Sigma.desc q)
           let c := radicialTripleThird (Sigma.desc q)
           let kab := Limits.pullback.lift a b (radicialTriple_first_second (Sigma.desc q))
           let kbc := Limits.pullback.lift b c (radicialTriple_second_third (Sigma.desc q))
           let kac := Limits.pullback.lift a c (radicialTriple_first_third (Sigma.desc q))
           reindexIso W θ kab a b
               (Limits.pullback.lift_fst _ _ _).symm
               (Limits.pullback.lift_snd _ _ _).symm ≪≫
             reindexIso W θ kbc b c
               (Limits.pullback.lift_fst _ _ _).symm
               (Limits.pullback.lift_snd _ _ _).symm =
           reindexIso W θ kac a c
             (Limits.pullback.lift_fst _ _ _).symm
             (Limits.pullback.lift_snd _ _ _).symm) ∧
          reindexIso W θ (Limits.pullback.diagonal (Sigma.desc q)) (𝟙 _) (𝟙 _)
            (Limits.pullback.diagonal_fst (Sigma.desc q)).symm
            (Limits.pullback.diagonal_snd (Sigma.desc q)).symm =
            Iso.refl ((FiniteEtale.pullback (𝟙 _)).obj W) := by
  classical
  intro r X₀ i V
  obtain ⟨m, Y, d, q, j, hj, hproper, hsurj, _⟩ :=
    exists_finite_integral_projective_cover f
  have hE (k : Fin m) :
      (FiniteEtale.pullback (Limits.pullback.fst (q k) i)).EssSurj := by
    have : IsClosedImmersion (j k) := (hj k).2.2.1
    exact closedProjective_component_essSurj R f (q k) (d k) (j k) (hj k).2.2.2
  let W (k : Fin m) : FiniteEtale (Y k) :=
    (FiniteEtale.pullback (Limits.pullback.fst (q k) i)).objPreimage
      ((FiniteEtale.pullback (Limits.pullback.snd (q k) i)).obj V)
  let e (k : Fin m) :
      (FiniteEtale.pullback (Limits.pullback.fst (q k) i)).obj (W k) ≅
        (FiniteEtale.pullback (Limits.pullback.snd (q k) i)).obj V :=
    (FiniteEtale.pullback (Limits.pullback.fst (q k) i)).objObjPreimageIso
      ((FiniteEtale.pullback (Limits.pullback.snd (q k) i)).obj V)
  obtain ⟨WSum, eSum⟩ := exists_sigma_comparison i m Y q V W e
  obtain ⟨eSum⟩ := eSum
  have : HenselianLocalRing R :=
    EtaleFundamentalGroups.henselianLocalRing_of_finiteEtale_local_of_isAdicComplete
      (R := R) (S := R)
  have : IsProper (Sigma.desc q) := hproper
  let θ := doubleOverlapIso (R := R) f (Sigma.desc q) WSum V eSum
  refine ⟨m, Y, d, q, j, hj, hproper, hsurj, WSum, eSum, θ, ?_⟩
  intro g e₁ e₂
  refine ⟨?_, ?_, ?_⟩
  · exact liftedIso_hom_restrict (R := R) (X := X) (Y := ∐ Y)
      (Z := Limits.pullback (Sigma.desc q) (Sigma.desc q))
      f (Sigma.desc q) g WSum V eSum
      (Limits.pullback.fst (Sigma.desc q) (Sigma.desc q)) rfl
      (Limits.pullback.snd (Sigma.desc q) (Sigma.desc q)) Limits.pullback.condition.symm
  · exact doubleOverlapIso_triple_cocycle (R := R) f (Sigma.desc q) WSum V eSum
  · exact doubleOverlapIso_diagonal (R := R) f (Sigma.desc q) WSum V eSum

end AlgebraicGeometry.FiniteEtale.ProperHenselianActionLifting
