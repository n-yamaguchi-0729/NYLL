/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperSeparablyClosedExtension
import Nyll.EtaleFundamentalGroups.GaloisCovers.IsomorphismTransport
import Nyll.EtaleFundamentalGroups.GaloisCovers.SurjectiveBaseChangeDescent
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Connected.Basic

/-!
# A proper geometric Galois cover over the relative separable closure

The specified separably closed field may contain inseparable elements or
be transcendental over the original field. Its relative separable closure
is an actual intermediate field and is itself separably closed. Proper
constant-field comparison descends the given finite étale cover to this
relative separable closure.

The actual coefficient-change square is cartesian and its projection is
surjective. This descends connectedness. Full faithfulness identifies the
actual deck-transformation groups, so the descended cover is Galois and
has exactly the original automorphism order. Thus the reduction preserves
the prime-to-characteristic condition without assuming the specified
geometric field is a separable extension of the original field.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

open EtaleFundamentalGroups

universe u

/-- A Galois cover of a proper geometric fibre descends to the actual
relative separable closure inside the specified field, with unchanged
automorphism order and an isomorphism recovering the original cover. -/
theorem exists_galois_model_over_relativeSeparableClosure
    (K Ω : Type u) [Field K] [Field Ω] [IsSepClosed Ω] [Algebra K Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsProper f] :
    let φΩ := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    let XΩ : Scheme.{u} := Limits.pullback φΩ f
    let pΩ : XΩ ⟶ Spec (.of Ω) := Limits.pullback.fst φΩ f
    let pX : XΩ ⟶ X := Limits.pullback.snd φΩ f
    ∀ [ConnectedSpace XΩ] (Z : FiniteEtale XΩ) [IsGalois Z],
      let S := separableClosure K Ω
      let φS := Spec.map (CommRingCat.ofHom (algebraMap K S))
      let XS : Scheme.{u} := Limits.pullback φS f
      let pS : XS ⟶ Spec (.of S) := Limits.pullback.fst φS f
      let b := Spec.map (CommRingCat.ofHom (algebraMap S Ω))
      ∃ hXS : ConnectedSpace XS,
        let : ConnectedSpace XS := hXS
        ∃ q : XΩ ⟶ XS,
          q ≫ Limits.pullback.snd φS f = pX ∧ IsPullback q pΩ pS b ∧
          ∃ Y : FiniteEtale XS, IsGalois Y ∧ Nat.card (Aut Y) = Nat.card (Aut Z) ∧
            Nonempty ((pullback q).obj Y ≅ Z) := by
  intro φΩ XΩ pΩ pX hXΩ Z hZ S φS XS pS b
  have : IsSepClosed S := (inferInstance : IsSepClosure K S).sep_closed
  have hCoeff : b ≫ φS = φΩ := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact S.val.comp_algebraMap
  let q : XΩ ⟶ XS := Limits.pullback.map φΩ f φS f b (𝟙 X) (𝟙 _)
    (by rw [Category.comp_id]; exact hCoeff.symm)
    (by rw [Category.comp_id, Category.id_comp])
  have hqFst : q ≫ pS = pΩ ≫ b := Limits.pullback.lift_fst _ _ _
  have hqSnd : q ≫ Limits.pullback.snd φS f = pX := by
    simp only [q, Limits.pullback.lift_snd, Category.comp_id, pX]
  have hOuter : IsPullback (q ≫ Limits.pullback.snd φS f) pΩ f (b ≫ φS) := by
    rw [hqSnd, hCoeff]
    exact (IsPullback.of_hasPullback φΩ f).flip
  have hq : IsPullback q pΩ pS b :=
    hOuter.of_right hqFst (IsPullback.of_hasPullback φS f).flip
  have hSurjB : Surjective b :=
    ⟨fun x ↦ ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ x⟩⟩
  have : Surjective q := MorphismProperty.of_isPullback (P := @Surjective) hq.flip hSurjB
  have hXS : ConnectedSpace XS := q.surjective.connectedSpace q.continuous
  have : IsProper pS := inferInstanceAs (IsProper (Limits.pullback.fst φS f))
  let F : FiniteEtale XS ⥤ FiniteEtale XΩ := pullback q
  have : F.IsEquivalence :=
    pullback_isEquivalence_of_isProper_of_isSepClosed_field_square S Ω
      (algebraMap S Ω) pS q pΩ hq
  let Y : FiniteEtale XS := F.objPreimage Z
  let eZ : F.obj Y ≅ Z := F.objObjPreimageIso Z
  have : IsGalois (F.obj Y) := isGalois_of_iso eZ.symm
  let eAut : Aut Y ≃* Aut (F.obj Y) :=
    (Functor.FullyFaithful.ofFullyFaithful F).autMulEquivOfFullyFaithful Y
  have hY : IsGalois Y :=
    (isGalois_iff_surjective_mapAut_of_surjective_baseChange q Y).mpr eAut.surjective
  have hCard : Nat.card (Aut Y) = Nat.card (Aut Z) :=
    (Nat.card_congr eAut.toEquiv).trans
      (Nat.card_congr (Aut.autMulEquivOfIso eZ).toEquiv)
  exact ⟨hXS, q, hqSnd, hq, Y, hY, hCard, ⟨eZ⟩⟩

end AlgebraicGeometry.FiniteEtale
