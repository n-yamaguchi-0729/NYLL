/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperAlgebraicallyClosedExtensionBaseChange
import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperAlgebraicallyClosedExtensionValuation
import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperHenselianFullyFaithful
import Nyll.SchemeTheory.Affine.FiniteSchemeScalarNaturality
import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Mathlib.Algebra.Algebra.Hom
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Recovery from the rational fibre of a proper constant model

The valuation ring connecting a rational coefficient point with the original
algebraically closed field gives two actual finite étale covers of the same
proper scheme over that ring. Their closed-fibre restrictions are isomorphic
by the proved residue triangle. Proper henselian full faithfulness lifts this
isomorphism, and restriction to the original field gives the recovery.

This is the geometric existence step of Stacks Project, Lemma 58.9.3,
https://stacks.math.columbia.edu/tag/0A49. No essential-surjectivity statement
over a henselian local base is assumed or used.
-/

noncomputable section

open CategoryTheory
open SchemeTheory.Affine.FiniteScheme

namespace AlgebraicGeometry.FiniteEtale

universe u

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

/-- For a proper scheme, a finite étale coefficient model over a subring of
an algebraically closed field is recovered from any rational coefficient
fibre after extending back to that same field. -/
theorem proper_rational_fiber_recovers_constant_model
    {k A K : Type u} [Field k] [CommRing A] [Field K] [IsAlgClosed K]
    [Algebra k A] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (t : A →ₐ[k] k) (ι : A →ₐ[k] K) (hι : Function.Injective ι)
    (N : FiniteEtale (Limits.pullback f (coefficientMap (K := k) A))) :
    Nonempty
      ((FiniteEtale.pullback
          (Limits.pullback.fst f (coefficientMap (K := k) K))).obj
          ((FiniteEtale.pullback (coefficientRationalPointMap f t)).obj N) ≅
        (FiniteEtale.pullback (coefficientPullbackMap f ι)).obj N) := by
  obtain ⟨V, g, hHenselian, hgeneric, hresidue⟩ :=
    exists_valuation_constant_specialization t ι hι
  have hV : HenselianLocalRing V := hHenselian
  let : Algebra k V := (g.comp (algebraMap k A)).toAlgebra
  let gA : A →ₐ[k] V :=
    { toRingHom := g
      commutes' := fun _ => rfl }
  let j : V →ₐ[k] K :=
    { toRingHom := algebraMap V K
      commutes' := fun r =>
        (RingHom.congr_fun hgeneric (algebraMap k A r)).trans (ι.commutes r) }
  have hjg : j.comp gA = ι := by
    apply AlgHom.ext
    intro a
    exact RingHom.congr_fun hgeneric a
  let XA : Scheme.{u} := Limits.pullback f (coefficientMap (K := k) A)
  let XV : Scheme.{u} := Limits.pullback f (coefficientMap (K := k) V)
  let XK : Scheme.{u} := Limits.pullback f (coefficientMap (K := k) K)
  let pA : XA ⟶ X := Limits.pullback.fst f (coefficientMap (K := k) A)
  let cA : XA ⟶ Spec (CommRingCat.of A) :=
    Limits.pullback.snd f (coefficientMap (K := k) A)
  let pV : XV ⟶ X := Limits.pullback.fst f (coefficientMap (K := k) V)
  let cV : XV ⟶ Spec (CommRingCat.of V) :=
    Limits.pullback.snd f (coefficientMap (K := k) V)
  let pK : XK ⟶ X := Limits.pullback.fst f (coefficientMap (K := k) K)
  let σ : XV ⟶ XA := coefficientPullbackMap f gA
  let a : X ⟶ XA := coefficientRationalPointMap f t
  let jX : XK ⟶ XV := coefficientPullbackMap f j
  let ρ : Spec (CommRingCat.of (IsLocalRing.ResidueField V)) ⟶
      Spec (CommRingCat.of V) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue V))
  let Y₀ : Scheme.{u} := Limits.pullback cV ρ
  let s : Y₀ ⟶ XV := Limits.pullback.fst cV ρ
  let z : Y₀ ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField V)) :=
    Limits.pullback.snd cV ρ
  have hproper : IsProper cV :=
    inferInstanceAs (IsProper (Limits.pullback.snd f (coefficientMap (K := k) V)))
  have hresidue' : (IsLocalRing.residue V).comp g =
      ((IsLocalRing.residue V).comp (algebraMap k V)).comp t.toRingHom := hresidue
  have hSpec : ρ ≫ Spec.map (CommRingCat.ofHom g) =
      (ρ ≫ coefficientMap (K := k) V) ≫
        Spec.map (CommRingCat.ofHom t.toRingHom) := by
    calc
      ρ ≫ Spec.map (CommRingCat.ofHom g) =
          Spec.map (CommRingCat.ofHom ((IsLocalRing.residue V).comp g)) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      _ = Spec.map (CommRingCat.ofHom
          (((IsLocalRing.residue V).comp (algebraMap k V)).comp t.toRingHom)) :=
        congrArg (fun h : A →+* IsLocalRing.ResidueField V =>
          Spec.map (CommRingCat.ofHom h)) hresidue'
      _ = (ρ ≫ coefficientMap (K := k) V) ≫
          Spec.map (CommRingCat.ofHom t.toRingHom) := by
        rw [← Spec.map_comp, ← Spec.map_comp,
          ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  have hσfst : σ ≫ pA = pV := coefficientPullbackMap_fst f gA
  have hafst : a ≫ pA = 𝟙 X := coefficientRationalPointMap_fst f t
  have hσsnd : σ ≫ cA = cV ≫ Spec.map (CommRingCat.ofHom g) :=
    coefficientPullbackMap_snd f gA
  have hasnd : a ≫ cA = f ≫ Spec.map (CommRingCat.ofHom t.toRingHom) :=
    coefficientRationalPointMap_snd f t
  have hs : s ≫ cV = z ≫ ρ := Limits.pullback.condition
  have hbase : pV ≫ f = cV ≫ coefficientMap (K := k) V := Limits.pullback.condition
  have hclosed : s ≫ σ = (s ≫ pV) ≫ a := by
    apply Limits.pullback.hom_ext
    · calc
        (s ≫ σ) ≫ pA = s ≫ pV := by rw [Category.assoc, hσfst]
        _ = ((s ≫ pV) ≫ a) ≫ pA := by
          rw [Category.assoc, hafst, Category.comp_id]
    · calc
        (s ≫ σ) ≫ cA = (s ≫ cV) ≫ Spec.map (CommRingCat.ofHom g) := by
          rw [Category.assoc, hσsnd, ← Category.assoc]
        _ = (z ≫ ρ) ≫ Spec.map (CommRingCat.ofHom g) :=
          congrArg (fun h : Y₀ ⟶ Spec (CommRingCat.of V) =>
            h ≫ Spec.map (CommRingCat.ofHom g)) hs
        _ = (z ≫ (ρ ≫ coefficientMap (K := k) V)) ≫
            Spec.map (CommRingCat.ofHom t.toRingHom) := by
          rw [Category.assoc, hSpec, ← Category.assoc]
        _ = ((s ≫ cV) ≫ coefficientMap (K := k) V) ≫
            Spec.map (CommRingCat.ofHom t.toRingHom) := by
          rw [← Category.assoc z ρ (coefficientMap (K := k) V), ← hs]
        _ = ((s ≫ pV) ≫ f) ≫ Spec.map (CommRingCat.ofHom t.toRingHom) := by
          rw [Category.assoc s cV (coefficientMap (K := k) V),
            ← hbase, ← Category.assoc s pV f]
        _ = ((s ≫ pV) ≫ a) ≫ cA := by
          rw [Category.assoc (s ≫ pV) a cA, hasnd,
            ← Category.assoc (s ≫ pV) f (Spec.map (CommRingCat.ofHom t.toRingHom))]
  let M : FiniteEtale X := (FiniteEtale.pullback a).obj N
  let NV : FiniteEtale XV := (FiniteEtale.pullback σ).obj N
  let MV : FiniteEtale XV := (FiniteEtale.pullback pV).obj M
  let eN₀ : (FiniteEtale.pullback (s ≫ σ)).obj N ≅
      (FiniteEtale.pullback s).obj NV :=
    (MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
      s σ (s ≫ σ) rfl).app N
  let eM₀ : (FiniteEtale.pullback (s ≫ σ)).obj N ≅
      (FiniteEtale.pullback (s ≫ pV)).obj M :=
    (MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
      (s ≫ pV) a (s ≫ σ) hclosed).app N
  let eM₁ : (FiniteEtale.pullback (s ≫ pV)).obj M ≅
      (FiniteEtale.pullback s).obj MV :=
    (MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
      s pV (s ≫ pV) rfl).app M
  let FF : (FiniteEtale.pullback s).FullyFaithful :=
    pullbackFullyFaithful_closedFiber_of_isProper_of_henselianLocalRing cV
  let eV : NV ≅ MV := FF.preimageIso (eN₀.symm ≪≫ eM₀ ≪≫ eM₁)
  have hgenericMap : coefficientPullbackMap f ι = jX ≫ σ :=
    ((coefficientPullbackMap_comp f gA j).trans
      (congrArg (fun h : A →ₐ[k] K => coefficientPullbackMap f h) hjg)).symm
  have hprojection : pK = jX ≫ pV := (coefficientPullbackMap_fst f j).symm
  let eNK : (FiniteEtale.pullback (coefficientPullbackMap f ι)).obj N ≅
      (FiniteEtale.pullback jX).obj NV :=
    (MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
      jX σ (coefficientPullbackMap f ι) hgenericMap).app N
  let eMK : (FiniteEtale.pullback pK).obj M ≅
      (FiniteEtale.pullback jX).obj MV :=
    (MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
      jX pV pK hprojection).app M
  exact ⟨eMK ≪≫ (FiniteEtale.pullback jX).mapIso eV.symm ≪≫ eNK.symm⟩

end AlgebraicGeometry.FiniteEtale
