/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Tactic.Set
public import Nyll.AbelianVarieties.Geometry.Quotients.Action
public import Nyll.AbelianVarieties.NeronModels.Endomorphisms
public import Nyll.SchemeTheory.Affine.OpenNeighborhoods
public import Nyll.AbelianVarieties.Basic
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Action
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Kernel
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Finite slices for a smooth subgroup action

The maximal finite locus of a transverse slice is stable under translations.
Its pullback relation is finite, flat, and locally of finite presentation on a nonempty slice.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_etale_isSeparated_quasiCompact_pullback_snd_action_slice.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem etale_isSeparated_quasiCompact_pullback_snd_action_slice
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (_hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (S : Scheme.{u}) (j : S ⟶ G) [IsAffine S] [Nonempty S] [LocallyOfFiniteType (j ≫ f)]
    (hEt : Etale (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i)) :
    Etale (pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ∧
    IsSeparated (pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ∧
    QuasiCompact (pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) := by
  have haf : (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) ≫ f =
        pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f := by
    have h1 : L.action i ≫ f = pullback.snd (i ≫ f) f ≫ f := L.action_over i
    rw [Category.assoc, h1, ← Category.assoc, pullback.lift_snd, Category.assoc]
  have : IsAffineHom (j ≫ f) := isAffineHom_of_isAffine _
  have hqc : QuasiCompact ((pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) ≫ f) := by
    rw [haf]; infer_instance
  have hsep : IsSeparated ((pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) ≫ f) := by
    rw [haf]; infer_instance
  have : QuasiCompact (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) :=
    .of_comp _ f
  have : IsSeparated (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) :=
    .of_comp _ f
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_action_slice_swap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem exists_iso_pullback_action_slice_swap
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (S : Scheme.{u}) (j : S ⟶ G) [IsAffine S] [Nonempty S] [LocallyOfFiniteType (j ≫ f)]
    (_hEt : Etale (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i)) :
    ∃ σ : pullback (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≅
        pullback (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j,
      σ.hom ≫ pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j =
        (pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ∧
      σ.hom ≫ (pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) =
        pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j := by
  classical
  set m : pullback (i ≫ f) (j ≫ f) ⟶ pullback (i ≫ f) f :=
    pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) with hm
  set a : pullback (i ≫ f) (j ≫ f) ⟶ G := m ≫ L.action i with ha
  set iG : SchemeHomOver (i ≫ f) f := ⟨i, rfl⟩ with hiG
  have hm₁ : m ≫ pullback.fst (i ≫ f) f = (pullback.fst (i ≫ f) (j ≫ f)) := by
    rw [hm, pullback.lift_fst, Category.comp_id]
  have hm₂ : m ≫ pullback.snd (i ≫ f) f = (pullback.snd (i ≫ f) (j ≫ f)) ≫ j := by
    rw [hm, pullback.lift_snd]
  have hP : (pullback.fst (i ≫ f) (j ≫ f)) ≫ i ≫ f = (pullback.snd (i ≫ f) (j ≫ f)) ≫ j ≫ f :=
      pullback.condition
  have haf : a ≫ f = (pullback.snd (i ≫ f) (j ≫ f)) ≫ j ≫ f := by
    rw [ha, Category.assoc, L.action_over i, ← Category.assoc, hm₂, Category.assoc]
  have hR : (pullback.fst a j) ≫ a = (pullback.snd a j) ≫ j := pullback.condition
  have ht1 : (pullback.fst a j) ≫ (pullback.snd (i ≫ f) (j ≫ f)) ≫ j ≫ f = (pullback.snd a j) ≫
      j ≫ f := by
    rw [← haf, ← Category.assoc, hR, Category.assoc]
  have ht2 : ((pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f))) ≫ i ≫ f = (pullback.snd a j) ≫
      j ≫ f := by rw [Category.assoc, hP, ht1]
  have a_pt : ∀ {T : Scheme.{u}} (ψ : T ⟶ pullback (i ≫ f) (j ≫ f))
      (t : T ⟶ Spec (CommRingCat.of k)) (ht : ψ ≫ (pullback.snd (i ≫ f) (j ≫ f)) ≫ j ≫ f = t)
      (h1 : (ψ ≫ (pullback.fst (i ≫ f) (j ≫ f))) ≫ i ≫ f = t) (h2 : (ψ ≫ (pullback.snd (i ≫ f)
          (j ≫ f)) ≫ j) ≫ f = t),
      ψ ≫ a = (L.mul t (NeronModelInfra.schemeHomOverComp (⟨ψ ≫ (pullback.fst (i ≫ f) (j ≫ f)),
          h1⟩ : SchemeHomOver t (i ≫ f)) iG)
        ⟨ψ ≫ (pullback.snd (i ≫ f) (j ≫ f)) ≫ j, h2⟩).1 := by
    intro T ψ t ht h1 h2
    have hψ : (ψ ≫ m) ≫ GoodReductionJacobian.RelativeGroupLaw.actionSource f i = t := by
      rw [GoodReductionJacobian.RelativeGroupLaw.actionSource, Category.assoc,
          ← Category.assoc m, hm₂,
        Category.assoc, ht]
    have := L.mul_natural _ t (ψ ≫ m) hψ (L.actionFstPoint i) (L.actionSndPoint i)
    rw [ha, ← Category.assoc]
    change (GoodReductionJacobian.schemeHomOverComp (ψ ≫ m) hψ
      (L.mul _ (L.actionFstPoint i) (L.actionSndPoint i))).1 = _
    rw [this]
    congr 2
    · apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe,
        GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe, Category.assoc, hiG]
      rw [← Category.assoc m, hm₁]
    · apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe,
        GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe]
      rw [Category.assoc, hm₂]
  have i_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
      NeronModelInfra.schemeHomOverComp (LN.one t) iG = L.one t := by
    intro T t
    have h2 := hi t (LN.one t) (LN.one t)
    rw [LN.one_mul] at h2
    calc NeronModelInfra.schemeHomOverComp (LN.one t) iG
        = L.mul t (L.one t) (NeronModelInfra.schemeHomOverComp (LN.one t) iG) :=
            (L.one_mul t _).symm
      _ = L.mul t (L.mul t (L.inv t (NeronModelInfra.schemeHomOverComp (LN.one t) iG))
            (NeronModelInfra.schemeHomOverComp (LN.one t) iG))
            (NeronModelInfra.schemeHomOverComp (LN.one t) iG) := by rw [L.inv_mul_cancel]
      _ = L.mul t (L.inv t (NeronModelInfra.schemeHomOverComp (LN.one t) iG))
            (L.mul t (NeronModelInfra.schemeHomOverComp (LN.one t) iG)
              (NeronModelInfra.schemeHomOverComp (LN.one t) iG)) := by rw [L.mul_assoc]
      _ = L.mul t (L.inv t (NeronModelInfra.schemeHomOverComp (LN.one t) iG))
            (NeronModelInfra.schemeHomOverComp (LN.one t) iG) := by rw [← h2]
      _ = L.one t := L.inv_mul_cancel t _
  have inv_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
      (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t
          (i ≫ f)),
      GoodReductionJacobian.schemeHomOverComp ψ hψ (LN.inv t x) =
        LN.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
    intro T T' t t' ψ hψ x
    have hyz : LN.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (LN.inv t x))
        (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = LN.one t' := by
      rw [← LN.mul_natural t t' ψ hψ, LN.inv_mul_cancel, LN.one_natural]
    calc GoodReductionJacobian.schemeHomOverComp ψ hψ (LN.inv t x)
        = LN.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (LN.inv t x)) (LN.one t') :=
          (LN.mul_one t' _).symm
      _ = LN.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (LN.inv t x))
            (LN.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x)
              (LN.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x))) :=
                  by rw [LN.mul_inv_cancel]
      _ = LN.mul t' (LN.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (LN.inv t x))
            (GoodReductionJacobian.schemeHomOverComp ψ hψ x))
            (LN.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x)) := by rw [LN.mul_assoc]
      _ = LN.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by rw [hyz, LN.one_mul]
  have hE : L.mul ((pullback.snd a j) ≫ j ≫ f)
      (NeronModelInfra.schemeHomOverComp (⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f)),
          ht2⟩ : SchemeHomOver ((pullback.snd a j) ≫ j ≫ f) (i ≫ f)) iG)
      ⟨(pullback.fst a j) ≫ (pullback.snd (i ≫ f) (j ≫ f)) ≫ j,
          by simp only [Category.assoc]; exact ht1⟩ =
      (⟨(pullback.snd a j) ≫ j, Category.assoc _ _ _⟩ : SchemeHomOver ((pullback.snd a j) ≫ j ≫
          f) f) := by
    apply Subtype.ext
    change _ = (pullback.snd a j) ≫ j
    rw [← hR, a_pt (pullback.fst a j) ((pullback.snd a j) ≫ j ≫ f) ht1 ht2]
  have hinv2 : (LN.inv ((pullback.snd a j) ≫ j ≫ f) ⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f)
      (j ≫ f)), ht2⟩).1 ≫ i ≫ f = (pullback.snd a j) ≫ j ≫ f :=
    (LN.inv ((pullback.snd a j) ≫ j ≫ f) ⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f)),
        ht2⟩).2
  set σP : pullback a j ⟶ pullback (i ≫ f) (j ≫ f) :=
    pullback.lift (f := i ≫ f) (g := j ≫ f)
      (LN.inv ((pullback.snd a j) ≫ j ≫ f) ⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f)),
          ht2⟩).1 (pullback.snd a j) hinv2 with hσP
  have hσP₁ : σP ≫ (pullback.fst (i ≫ f) (j ≫ f)) = (LN.inv ((pullback.snd a j) ≫ j ≫
      f) ⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f)), ht2⟩).1 := by
    rw [hσP]; exact pullback.lift_fst _ _ _
  have hσP₂ : σP ≫ (pullback.snd (i ≫ f) (j ≫ f)) = (pullback.snd a j) :=
      by rw [hσP]; exact pullback.lift_snd _ _ _
  have hσPt : σP ≫ (pullback.snd (i ≫ f) (j ≫ f)) ≫ j ≫ f = (pullback.snd a j) ≫ j ≫ f :=
      by rw [← Category.assoc, hσP₂]
  have hσP1' : (σP ≫ (pullback.fst (i ≫ f) (j ≫ f))) ≫ i ≫ f = (pullback.snd a j) ≫ j ≫ f :=
      by rw [hσP₁]; exact hinv2
  have hσP2' : (σP ≫ (pullback.snd (i ≫ f) (j ≫ f)) ≫ j) ≫ f = (pullback.snd a j) ≫ j ≫ f :=
      by rw [Category.assoc, Category.assoc, hσPt]
  have w2 : σP ≫ a = ((pullback.fst a j) ≫ (pullback.snd (i ≫ f) (j ≫ f))) ≫ j := by
    rw [a_pt σP ((pullback.snd a j) ≫ j ≫ f) hσPt hσP1' hσP2']
    have e1 : (NeronModelInfra.schemeHomOverComp (⟨σP ≫ (pullback.fst (i ≫ f) (j ≫ f)),
        hσP1'⟩ : SchemeHomOver ((pullback.snd a j) ≫ j ≫ f) (i ≫ f)) iG)
        = NeronModelInfra.schemeHomOverComp (LN.inv ((pullback.snd a j) ≫ j ≫
            f) ⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f)), ht2⟩) iG := by
      congr 1; exact Subtype.ext hσP₁
    have e2 : (⟨σP ≫ (pullback.snd (i ≫ f) (j ≫ f)) ≫ j,
        hσP2'⟩ : SchemeHomOver ((pullback.snd a j) ≫ j ≫ f) f) = ⟨(pullback.snd a j) ≫ j,
        Category.assoc _ _ _⟩ :=
      Subtype.ext (by simp only; rw [← Category.assoc, hσP₂])
    rw [e1, e2, ← hE, ← L.mul_assoc, ← hi, LN.inv_mul_cancel, i_one, L.one_mul]
    exact (Category.assoc _ _ _).symm
  set σ : pullback a j ⟶ pullback a j :=
    pullback.lift (f := a) (g := j) σP ((pullback.fst a j) ≫ (pullback.snd (i ≫ f) (j ≫
        f))) w2 with hσ
  have hσ₁ : σ ≫ (pullback.fst a j) = σP := by rw [hσ]; exact pullback.lift_fst _ _ _
  have hσ₂ : σ ≫ (pullback.snd a j) = (pullback.fst a j) ≫ (pullback.snd (i ≫ f) (j ≫ f)) :=
      by rw [hσ]; exact pullback.lift_snd _ _ _
  have hσt : σ ≫ (pullback.snd a j) ≫ j ≫ f = (pullback.snd a j) ≫ j ≫ f :=
      by rw [← Category.assoc, hσ₂, Category.assoc, ht1]
  have σσ : σ ≫ σ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, hσ₁]
      apply pullback.hom_ext
      · rw [Category.assoc, hσP₁]
        have := inv_natural ((pullback.snd a j) ≫ j ≫ f) ((pullback.snd a j) ≫ j ≫
            f) σ hσt ⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f)), ht2⟩
        have e3 : GoodReductionJacobian.schemeHomOverComp σ hσt (⟨(pullback.fst a j) ≫
            (pullback.fst (i ≫ f) (j ≫ f)), ht2⟩ : SchemeHomOver _ (i ≫ f)) =
            LN.inv ((pullback.snd a j) ≫ j ≫ f) ⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫
                f)), ht2⟩ :=
          Subtype.ext (by
            simp only [GoodReductionJacobian.schemeHomOverComp_coe]
            rw [← Category.assoc, hσ₁, hσP₁])
        rw [e3] at this
        have e4 : LN.inv ((pullback.snd a j) ≫ j ≫ f) (LN.inv ((pullback.snd a j) ≫ j ≫
            f) ⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f)),
            ht2⟩) = ⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f)), ht2⟩ := by
          let : Group (SchemeHomOver ((pullback.snd a j) ≫ j ≫ f) (i ≫ f)) :=
            LN.pointGroup ((pullback.snd a j) ≫ j ≫ f)
          exact inv_inv _
        rw [e4] at this
        exact congrArg Subtype.val this
      · rw [Category.assoc, hσP₂, hσ₂]
    · rw [Category.id_comp, Category.assoc, hσ₂, ← Category.assoc, hσ₁, hσP₂]
  refine ⟨⟨σ, σ, σσ, σσ⟩, ?_, ?_⟩
  · exact hσ₂
  · rw [← Category.assoc, hσ₁, hσP₂]

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_isFinite_morphismRestrict_action_slice_maximal_stable.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.FiniteSliceLocus

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace FiniteLocus

section Points

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f)) {S : Scheme.{u}} (j : S ⟶ G)

/-- The action of the subgroup on the chosen slice. -/
abbrev amap : pullback (i ≫ f) (j ≫ f) ⟶ G :=
  pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i

theorem mul_coe_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of k)} (h : t = t')
    (x y : SchemeHomOver t f) (x' y' : SchemeHomOver t' f) (hx : x.1 = x'.1) (hy : y.1 = y'.1) :
    (L.mul t x y).1 = (L.mul t' x' y').1 := by
  subst h
  obtain rfl : x = x' := Subtype.ext hx
  obtain rfl : y = y' := Subtype.ext hy
  rfl

/-- View a subgroup-valued point as a point of the ambient group. -/
def ipt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (n : SchemeHomOver t (i ≫
    f)) : SchemeHomOver t f :=
  ⟨n.1 ≫ i, by rw [Category.assoc]; exact n.2⟩

@[scoped simp] theorem ipt_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (n : SchemeHomOver t (i ≫ f)) :
    (ipt i n).1 = n.1 ≫ i := rfl

theorem ipt_eq_comp {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (n : SchemeHomOver t (i ≫
    f)) :
    ipt i n = NeronModelInfra.schemeHomOverComp n (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) := rfl

/-- Pair a subgroup point with a point of the slice. -/
def pairNS {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (n : SchemeHomOver t (i ≫ f))
    (s : T ⟶ S)
    (hs : s ≫ j ≫ f = t) : T ⟶ pullback (i ≫ f) (j ≫ f) :=
  pullback.lift n.1 s (by rw [n.2, hs])

@[scoped simp] theorem pairNS_fst {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (n : SchemeHomOver t (i ≫ f))
    (s : T ⟶ S) (hs : s ≫ j ≫ f = t) : pairNS i j n s hs ≫ pullback.fst _ _ = n.1 :=
        pullback.lift_fst _ _ _

@[scoped simp] theorem pairNS_snd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (n : SchemeHomOver t (i ≫ f))
    (s : T ⟶ S) (hs : s ≫ j ≫ f = t) : pairNS i j n s hs ≫ pullback.snd _ _ = s :=
        pullback.lift_snd _ _ _

theorem comp_amap {T : Scheme.{u}} (z : T ⟶ pullback (i ≫ f) (j ≫ f)) (t : T ⟶ Spec
    (CommRingCat.of k))
    (ht : z ≫ pullback.fst _ _ ≫ i ≫ f = t) :
    z ≫ amap L i j =
      (L.mul t (ipt i ⟨z ≫ pullback.fst _ _, ht⟩)
        ⟨z ≫ pullback.snd _ _ ≫ j, by
          rw [Category.assoc, Category.assoc, ← pullback.condition]; exact ht⟩).1 := by
  set m := pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) with hm
  have hm_snd : m ≫ pullback.snd (i ≫ f) f = pullback.snd _ _ ≫ j := by
    rw [hm]; exact pullback.lift_snd _ _ _
  have hm_fst : m ≫ pullback.fst (i ≫ f) f = pullback.fst _ _ ≫ 𝟙 N := by
    rw [hm]; exact pullback.lift_fst _ _ _
  have hz : (z ≫ m) ≫ RelativeGroupLaw.actionSource f i = t := by
    change (z ≫ m) ≫ pullback.snd (i ≫ f) f ≫ f = t
    rw [Category.assoc, ← Category.assoc m, hm_snd]
    simp only [Category.assoc]
    rw [← pullback.condition]
    exact ht
  change z ≫ m ≫ L.action i = _
  rw [RelativeGroupLaw.action_def, ← Category.assoc]
  have h1 := congrArg Subtype.val
    (L.mul_natural (RelativeGroupLaw.actionSource f i) t (z ≫ m) hz (L.actionFstPoint i)
        (L.actionSndPoint i))
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h1
  rw [h1]
  apply mul_coe_congr L rfl
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.actionFstPoint_coe,
      ipt_coe,
      Category.assoc]
    rw [← Category.assoc m, hm_fst, Category.comp_id]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.actionSndPoint_coe,
      Category.assoc]
    rw [hm_snd]

theorem pairNS_amap {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (n : SchemeHomOver t (i ≫ f))
    (s : T ⟶ S) (hs : s ≫ j ≫ f = t) :
    pairNS i j n s hs ≫ amap L i j = (L.mul t (ipt i n) ⟨s ≫ j, hs⟩).1 := by
  rw [comp_amap L i j (pairNS i j n s hs) t (by rw [← Category.assoc, pairNS_fst, n.2])]
  apply mul_coe_congr L rfl
  · simp only [ipt_coe]; rw [pairNS_fst]
  · change (pairNS i j n s hs ≫ pullback.snd _ _) ≫ j = s ≫ j
    rw [pairNS_snd]

theorem ipt_mul
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)) :
    ipt i (LN.mul t x y) = L.mul t (ipt i x) (ipt i y) := by
  simp only [ipt_eq_comp]; exact hi t x y

theorem ipt_injective [IsClosedImmersion i] {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (x y : SchemeHomOver t (i ≫ f)) (h : ipt i x = ipt i y) : x = y := by
  apply Subtype.ext
  have := congrArg Subtype.val h
  simp only [ipt_coe] at this
  exact (cancel_mono i).1 this

end Points

section Translations

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f)) {S : Scheme.{u}} (j : S ⟶ G)

variable (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))

include hi in
theorem ipt_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    ipt i (LN.one t) = L.one t :=
  AbelianVarieties.NOSProofs.QuotientEquivalence.SubgroupAction.hom_one L i LN hi t

include hi in
theorem ipt_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (m : SchemeHomOver t (i ≫ f)) : ipt i (LN.inv t m) = L.inv t (ipt i m) :=
  AbelianVarieties.NOSProofs.QuotientEquivalence.SubgroupAction.hom_inv L i LN hi t m

omit LN in
theorem amap_over : amap L i j ≫ f = pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f := by
  change (pullback.map _ _ _ _ _ _ _ _ _ ≫ L.action i) ≫ f = _
  rw [Category.assoc, RelativeGroupLaw.action_over, RelativeGroupLaw.actionSource, ← Category.assoc,
    pullback.lift_snd, Category.assoc]

omit LN in
theorem amap_over' : amap L i j ≫ f = pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫ f := by
  rw [amap_over, pullback.condition]

end Translations

section Generic

variable {k : Type u} [Field k] {H : Scheme.{u}} {g : H ⟶ Spec (CommRingCat.of k)}
    (M : RelativeGroupLaw k g)

/-- The constant point obtained by base change. -/
def cst (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) : SchemeHomOver g g :=
  GoodReductionJacobian.schemeHomOverComp g (Category.comp_id g) P

@[scoped simp] theorem cst_coe (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) : (cst P).1 =
    g ≫ P.1 := rfl

/-- The tautological point of the group scheme. -/
def idpt : SchemeHomOver g g := ⟨𝟙 H, Category.id_comp _⟩

@[scoped simp] theorem idpt_coe : (idpt : SchemeHomOver g g).1 = 𝟙 H := rfl

/-- Translation of the group scheme by a rational point. -/
def trans (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) : H ⟶ H :=
    (M.mul g (cst P) idpt).1

theorem trans_over (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) : trans M P ≫ g = g :=
    (M.mul g (cst P) idpt).2

theorem comp_trans (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (x : T ⟶ H) (hx : x ≫ g = t) :
    x ≫ trans M P = (M.mul t ⟨t ≫ P.1,
        by rw [Category.assoc, P.2, Category.comp_id]⟩ ⟨x, hx⟩).1 := by
  have h := congrArg Subtype.val (M.mul_natural g t x hx (cst P) idpt)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  unfold trans
  rw [h]
  apply mul_coe_congr M rfl
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, cst_coe, ← Category.assoc, hx]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, idpt_coe, Category.comp_id]

theorem cst_mul (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) :
    M.mul g (cst Q) (cst P) = cst (M.mul (𝟙 _) Q P) := by
  unfold cst
  exact (M.mul_natural (𝟙 _) g g (Category.comp_id g) Q P).symm

theorem cst_one : cst (M.one (𝟙 (Spec (CommRingCat.of k)))) = (M.one g : SchemeHomOver g g) := by
  unfold cst
  exact M.one_natural (𝟙 _) g g (Category.comp_id g)

theorem trans_trans (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) :
    trans M P ≫ trans M Q = trans M (M.mul (𝟙 _) Q P) := by
  rw [comp_trans M Q g (trans M P) (trans_over M P)]
  have hP : (⟨trans M P, trans_over M P⟩ : SchemeHomOver g g) = M.mul g (cst P) idpt :=
    Subtype.ext rfl
  have hQ : (⟨g ≫ Q.1, by rw [Category.assoc, Q.2, Category.comp_id]⟩ :
      SchemeHomOver g g) = cst Q :=
    Subtype.ext rfl
  rw [hP, hQ, ← M.mul_assoc, cst_mul]
  rfl

theorem trans_one : trans M (M.one (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 H := by
  unfold trans
  rw [cst_one, M.one_mul]
  rfl

theorem trans_inv_comp (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) :
    trans M P ≫ trans M (M.inv (𝟙 _) P) = 𝟙 H := by
  rw [trans_trans, M.inv_mul_cancel, trans_one]

theorem trans_comp_inv (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) :
    trans M (M.inv (𝟙 _) P) ≫ trans M P = 𝟙 H := by
  rw [trans_trans, M.mul_inv_cancel, trans_one]

/-- Translation by a rational point as a scheme isomorphism. -/
def transIso (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) : H ≅ H where
  hom := trans M P
  inv := trans M (M.inv (𝟙 _) P)
  hom_inv_id := trans_inv_comp M P
  inv_hom_id := trans_comp_inv M P

scoped instance isIso_trans (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) : IsIso
    (trans M P) :=
  (transIso M P).isIso_hom

end Generic

section Equivariance

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f)) {S : Scheme.{u}} (j : S ⟶ G)

variable (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))

/-- Translation on the subgroup factor of the slice product. -/
def transNS (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f)) :
    pullback (i ≫ f) (j ≫ f) ⟶ pullback (i ≫ f) (j ≫ f) :=
  pullback.map (i ≫ f) (j ≫ f) (i ≫ f) (j ≫ f) (trans LN Q) (𝟙 S) (𝟙 _)
    (by rw [Category.comp_id, trans_over]) (by rw [Category.comp_id, Category.id_comp])

scoped instance isIso_transNS (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f)) : IsIso
    (transNS i LN j Q) := by
  unfold transNS
  infer_instance

theorem transNS_fst (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f)) :
    transNS i LN j Q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ trans LN Q := pullback.lift_fst _ _ _

theorem transNS_snd (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f)) :
    transNS i LN j Q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ 𝟙 S := pullback.lift_snd _ _ _

include hi in
theorem amap_trans (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f)) :
    amap L i j ≫ trans L (ipt i Q) = transNS i LN j Q ≫ amap L i j := by
  have ht' : transNS i LN j Q ≫ pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫ f = pullback.fst (i ≫ f) (j ≫
      f) ≫ i ≫ f := by
    rw [← Category.assoc, transNS_fst, Category.assoc, trans_over]
  rw [comp_amap L i j (transNS i LN j Q) _ ht',
    comp_trans L (ipt i Q) (pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫ f) (amap L i j) (amap_over' L i j)]
  have ha : (⟨amap L i j, amap_over' L i j⟩ : SchemeHomOver (pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫
      f) f) =
      L.mul _ (ipt i ⟨pullback.fst (i ≫ f) (j ≫ f), rfl⟩)
        ⟨pullback.snd (i ≫ f) (j ≫ f) ≫ j, by rw [Category.assoc, ← pullback.condition]⟩ := by
    apply Subtype.ext
    have := comp_amap L i j (𝟙 _) (pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫ f) (by rw [Category.id_comp])
    rw [Category.id_comp] at this
    change amap L i j = _
    rw [this]
    apply mul_coe_congr L rfl
    · simp only [ipt_coe, Category.id_comp]
    · change 𝟙 _ ≫ pullback.snd _ _ ≫ j = pullback.snd _ _ ≫ j
      rw [Category.id_comp]
  have hN : (ipt i ⟨transNS i LN j Q ≫ pullback.fst (i ≫ f) (j ≫ f), ht'⟩ :
      SchemeHomOver (pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫ f) f) =
      L.mul _ ⟨(pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫ f) ≫ (ipt i Q).1, by
          rw [Category.assoc, (ipt i Q).2, Category.comp_id]⟩
        (ipt i ⟨pullback.fst (i ≫ f) (j ≫ f), rfl⟩) := by
    have h1 : (⟨transNS i LN j Q ≫ pullback.fst (i ≫ f) (j ≫ f), ht'⟩ :
        SchemeHomOver (pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫ f) (i ≫ f)) =
        LN.mul _ ⟨(pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫ f) ≫ Q.1,
            by rw [Category.assoc, Q.2, Category.comp_id]⟩
          ⟨pullback.fst (i ≫ f) (j ≫ f), rfl⟩ := by
      apply Subtype.ext
      change transNS i LN j Q ≫ pullback.fst (i ≫ f) (j ≫ f) = _
      rw [transNS_fst, comp_trans LN Q _ _ rfl]
    rw [h1, ipt_mul L i LN hi]
    congr 1
  rw [ha, hN, L.mul_assoc]
  apply mul_coe_congr L rfl _ _ _ _ rfl
  apply mul_coe_congr L rfl _ _ _ _ rfl
  change pullback.snd (i ≫ f) (j ≫ f) ≫ j = transNS i LN j Q ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j
  rw [← Category.assoc, transNS_snd, Category.comp_id]

omit LN hi in
theorem preimage_mono' {X Y : Scheme.{u}} (a : X ⟶ Y) {U V : Y.Opens} (h : U ≤ V) :
    a ⁻¹ᵁ U ≤ a ⁻¹ᵁ V := fun _ hx => h hx

omit LN hi in
theorem isFinite_restrict_congr {X Y : Scheme.{u}} {a b : X ⟶ Y} (e : a = b) (W : Y.Opens)
    (h : IsFinite (a ∣_ W)) :
    IsFinite (b ∣_ W) := by
  subst e; exact h

include hi in
theorem isFinite_restrict_preimage_trans (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f))
    (W : G.Opens) (hW : IsFinite (amap L i j ∣_ W)) :
    IsFinite (amap L i j ∣_ (trans L (ipt i Q) ⁻¹ᵁ W)) := by
  have hFiniteLocal : IsZariskiLocalAtTarget
      (@IsFinite : MorphismProperty Scheme.{u}) := AlgebraicGeometry.isFiniteLocalAtTarget
  have : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    hFiniteLocal.toRespects
  have : IsFinite (transNS i LN j Q) := MorphismProperty.of_isIso @IsFinite _
  have h1 : IsFinite ((transNS i LN j Q ≫ amap L i j) ∣_ W) := by
    rw [morphismRestrict_comp]
    exact MorphismProperty.comp_mem @IsFinite _ _ (IsZariskiLocalAtTarget.restrict (P :=
        @IsFinite) ‹IsFinite (transNS i LN j Q)› _) hW
  have h2 : IsFinite ((amap L i j ≫ trans L (ipt i Q)) ∣_ W) :=
    isFinite_restrict_congr (amap_trans L i LN j hi Q).symm W h1
  rw [morphismRestrict_comp] at h2
  exact (MorphismProperty.cancel_right_of_respectsIso @IsFinite _ _).1 h2

end Equivariance

end FiniteLocus

end

end AbelianVarieties.NOSProofs.FiniteSliceLocus

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u
open AbelianVarieties.NOSProofs.FiniteSliceLocus.FiniteLocus

theorem exists_opens_isFinite_morphismRestrict_action_slice_maximal_stable
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (S : Scheme.{u}) (j : S ⟶ G) [IsAffine S] [Nonempty S] [LocallyOfFiniteType (j ≫ f)]
    (_hEt : Etale (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i)) :
    ∃ U : G.Opens,
      IsFinite ((pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) ∣_ U) ∧
      (∀ W : G.Opens, IsFinite ((pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) ∣_ W) → W ≤ U) ∧
      (∀ (n : Spec (CommRingCat.of k) ⟶ N) (hn : n ≫ i ≫ f = 𝟙 _),
        (L.mul f ⟨f ≫ n ≫ i, by
          rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G,
              Category.id_comp _⟩).1 ⁻¹ᵁ U = U) := by
  have hFiniteLocal : IsZariskiLocalAtTarget
      (@IsFinite : MorphismProperty Scheme.{u}) := AlgebraicGeometry.isFiniteLocalAtTarget
  have : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    hFiniteLocal.toRespects
  refine ⟨sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)}, ?_, fun W hW => le_sSup hW, ?_⟩
  · apply IsZariskiLocalAtTarget.of_iSup_eq_top
      (fun W : {W : G.Opens // IsFinite (amap L i j ∣_ W)} =>
        (sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)}).ι ⁻¹ᵁ W.1)
    · rw [← Scheme.Hom.preimage_iSup]
      have hs : (⨆ W : {W : G.Opens // IsFinite (amap L i j ∣_ W)}, W.1) =
          sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)} := (sSup_eq_iSup' _).symm
      rw [hs]
      exact Scheme.Opens.ι_preimage_self _
    · rintro ⟨W, hW⟩
      have hle : W ≤ sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)} := le_sSup hW
      have heq : (sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)}).ι ''ᵁ
          ((sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)}).ι ⁻¹ᵁ W) = W := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right]
        exact hle
      have h : IsFinite (amap L i j ∣_ ((sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)}).ι ''ᵁ
          ((sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)}).ι ⁻¹ᵁ W))) := by rw [heq]; exact hW
      exact (MorphismProperty.arrow_mk_iso_iff @IsFinite (morphismRestrictRestrict _ _ _)).2 h
  · intro n hn
    have key : ∀ (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f)),
        trans L (ipt i Q) ⁻¹ᵁ sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)} ≤
          sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)} := by
      intro Q
      rw [sSup_eq_iSup', Scheme.Hom.preimage_iSup]
      refine iSup_le fun W => ?_
      rw [← sSup_eq_iSup']
      exact le_sSup (isFinite_restrict_preimage_trans L i LN j hi Q W.1 W.2)
    have htr : (L.mul f ⟨f ≫ n ≫ i, by
          rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G, Category.id_comp _⟩).1 =
        trans L (ipt i ⟨n, hn⟩) := rfl
    rw [htr]
    apply le_antisymm (key ⟨n, hn⟩)
    have hinv := key (LN.inv (𝟙 _) ⟨n, hn⟩)
    have hcomp : trans L (ipt i ⟨n, hn⟩) ≫ trans L (ipt i (LN.inv (𝟙 _) ⟨n, hn⟩)) = 𝟙 G := by
      rw [ipt_inv L i LN hi, trans_inv_comp]
    calc sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)}
        = (trans L (ipt i ⟨n, hn⟩) ≫ trans L (ipt i (LN.inv (𝟙 _) ⟨n, hn⟩))) ⁻¹ᵁ
            sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)} := by rw [hcomp]; rfl
      _ = trans L (ipt i ⟨n, hn⟩) ⁻¹ᵁ (trans L (ipt i (LN.inv (𝟙 _) ⟨n, hn⟩)) ⁻¹ᵁ
            sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)}) := rfl
      _ ≤ trans L (ipt i ⟨n, hn⟩) ⁻¹ᵁ sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)} :=
            preimage_mono' _ hinv

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_preimage_eq_preimage_and_isFinite_pullback_snd_action_slice_of_stable.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.StableSliceRelation

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace StableRelation

theorem comp_base_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).base x = g.base (f.base x) := rfl

theorem opens_eq_of_forall_isClosed_iff {X : Type u} [TopologicalSpace X] [JacobsonSpace X]
    {O₁ O₂ : TopologicalSpace.Opens X}
    (h : ∀ x : X, IsClosed ({x} : Set X) → (x ∈ O₁ ↔ x ∈ O₂)) : O₁ = O₂ := by
  have key : ∀ {P Q : TopologicalSpace.Opens X},
      (∀ x : X, IsClosed ({x} : Set X) → x ∈ P → x ∈ Q) → P ≤ Q := by
    intro P Q hPQ x hxP
    by_contra hxQ
    obtain ⟨y, ⟨hyP, hyQ⟩, hycl⟩ :=
      nonempty_inter_closedPoints (Z := (P : Set X) ∩ (Q : Set X)ᶜ) ⟨x, hxP, hxQ⟩
        (P.2.isLocallyClosed.inter Q.2.isClosed_compl.isLocallyClosed)
    exact hyQ (hPQ y hycl hyP)
  exact le_antisymm (key fun x hx => (h x hx).1) (key fun x hx => (h x hx).2)

theorem pullback_snd_congr (P : MorphismProperty Scheme.{u}) {X Y Z : Scheme.{u}} (f : X ⟶ Z)
    {g g' : Y ⟶ Z} (e : g = g') (h : P (pullback.snd f g)) : P (pullback.snd f g') := by
  subst e; exact h

theorem morphismRestrict_pullback_snd (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    [P.IsStableUnderBaseChange] {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (U : Z.Opens)
    (hf : P (f ∣_ U)) : P (pullback.snd f g ∣_ (g ⁻¹ᵁ U)) := by
  have h1 : P (pullback.snd f U.ι) := by
    delta morphismRestrict at hf
    rwa [P.cancel_left_of_respectsIso] at hf
  have h2 : P (pullback.snd (pullback.snd f U.ι) (g ∣_ U)) := P.pullback_snd _ _ h1
  rw [← pullbackLeftPullbackSndIso_hom_snd f U.ι (g ∣_ U), P.cancel_left_of_respectsIso] at h2
  have h3 : P (pullback.snd f ((g ⁻¹ᵁ U).ι ≫ g)) :=
      pullback_snd_congr P f (morphismRestrict_ι g U) h2
  delta morphismRestrict
  rw [P.cancel_left_of_respectsIso]
  rw [← pullbackLeftPullbackSndIso_hom_snd f g (g ⁻¹ᵁ U).ι, P.cancel_left_of_respectsIso]
  exact h3

section GroupLaw

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f)

theorem mul_val_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of k)} (e : t = t')
    (x y : SchemeHomOver t f) (x' y' : SchemeHomOver t' f) (hx : x.1 = x'.1) (hy : y.1 = y'.1) :
    (L.mul t x y).1 = (L.mul t' x' y').1 :=
  AbelianVarieties.NOSProofs.FiniteSliceLocus.FiniteLocus.mul_coe_congr L e x y x' y' hx hy

theorem comp_translation {N : Scheme.{u}} (i : N ⟶ G) (n : Spec (CommRingCat.of k) ⟶ N)
    (hn : n ≫ i ≫ f = 𝟙 _) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : T ⟶ G)
        (hx : x ≫ f = t) :
    x ≫ (L.mul f ⟨f ≫ n ≫ i, by
          rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G, Category.id_comp _⟩).1 =
      (L.mul t ⟨t ≫ n ≫ i, by
          rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨x, hx⟩).1 := by
  have h := congrArg Subtype.val
    (L.mul_natural f t x hx ⟨f ≫ n ≫ i, by
          rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩
      ⟨𝟙 G, Category.id_comp _⟩)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  rw [h]
  apply mul_val_congr L rfl
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc, hx]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, Category.comp_id]

/-- The action map on the product of the subgroup and slice. -/
noncomputable abbrev amap {N S : Scheme.{u}} (i : N ⟶ G) (j : S ⟶ G) : pullback (i ≫ f) (j ≫
    f) ⟶ G :=
  pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i

theorem comp_action {N S : Scheme.{u}} (i : N ⟶ G) (j : S ⟶ G) {T : Scheme.{u}}
    (ζ : T ⟶ pullback (i ≫ f) (j ≫ f)) :
    ζ ≫ amap L i j =
      (L.mul (ζ ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f)
        ⟨ζ ≫ pullback.fst (i ≫ f) (j ≫ f) ≫ i, by
          simp only [Category.assoc]; rw [pullback.condition]⟩
        ⟨ζ ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j, by simp only [Category.assoc]⟩).1 := by
  have hfst : pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
        ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
      pullback.fst (i ≫ f) f = pullback.fst (i ≫ f) (j ≫ f) ≫ 𝟙 N :=
    pullback.lift_fst _ _ _
  have hsnd : pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
        ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
      pullback.snd (i ≫ f) f = pullback.snd (i ≫ f) (j ≫ f) ≫ j :=
    pullback.lift_snd _ _ _
  change ζ ≫ (_ ≫ L.action i) = _
  rw [← Category.assoc, L.action_def]
  have h := congrArg Subtype.val
    (L.mul_natural (RelativeGroupLaw.actionSource f i) _
      (ζ ≫ pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _)) rfl
      (L.actionFstPoint i) (L.actionSndPoint i))
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  rw [h]
  apply mul_val_congr L
  · simp only [RelativeGroupLaw.actionSource, Category.assoc, reassoc_of% hsnd]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.actionFstPoint_coe,
      Category.assoc,
      reassoc_of% hfst]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.actionSndPoint_coe,
      Category.assoc,
      hsnd]

theorem amap_over {N S : Scheme.{u}} (i : N ⟶ G) (j : S ⟶ G) :
    amap L i j ≫ f = pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f := by
  change (pullback.map _ _ _ _ _ _ _ _ _ ≫ L.action i) ≫ f = _
  rw [Category.assoc, RelativeGroupLaw.action_over, RelativeGroupLaw.actionSource, ← Category.assoc,
    pullback.lift_snd, Category.assoc]

theorem preimage_fst_snd_eq_preimage_snd [IsAlgClosed k] {N S : Scheme.{u}} (i : N ⟶ G) (j : S ⟶ G)
    [LocallyOfFiniteType (j ≫ f)] (hEt : Etale (amap L i j)) (U : G.Opens)
    (hUstab : ∀ (n : Spec (CommRingCat.of k) ⟶ N) (hn : n ≫ i ≫ f = 𝟙 _),
      (L.mul f ⟨f ≫ n ≫ i, by
          rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩
        ⟨𝟙 G, Category.id_comp _⟩).1 ⁻¹ᵁ U = U) :
    (pullback.fst (amap L i j) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ (j ⁻¹ᵁ U) =
      (pullback.snd (amap L i j) j) ⁻¹ᵁ (j ⁻¹ᵁ U) := by
  have : LocallyOfFiniteType (amap L i j) := inferInstance
  have : JacobsonSpace ↥(pullback (amap L i j) j) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd (amap L i j) j ≫ j ≫ f)
  apply opens_eq_of_forall_isClosed_iff
  intro z hz
  set ρ := pointOfClosedPoint (pullback.snd (amap L i j) j ≫ j ≫ f) z hz with hρ
  have hρq : ρ ≫ pullback.snd (amap L i j) j ≫ j ≫ f = 𝟙 _ := pointOfClosedPoint_comp _ z hz
  have hρpt : ρ.base ((show Spec (CommRingCat.of k) from IsLocalRing.closedPoint k)) = z :=
      pointOfClosedPoint_apply _ z hz _
  have hp2 : ρ ≫ pullback.snd (amap L i j) j ≫ j = (ρ ≫ pullback.fst (amap L i j) j) ≫
      amap L i j := by
    rw [Category.assoc, pullback.condition]
  have hζq : (ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f = 𝟙 _ := by
    rw [← amap_over L i j, ← Category.assoc, ← hp2, Category.assoc]
    exact hρq
  have hn : ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.fst (i ≫ f) (j ≫ f)) ≫ i ≫ f = 𝟙 _ := by
    rw [Category.assoc, pullback.condition]; exact hζq
  have hx : ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j) ≫ f = 𝟙 _ := by
    simpa only [Category.assoc] using hζq
  have h1 := comp_action L i j (ρ ≫ pullback.fst (amap L i j) j)
  have h2 := comp_translation L i ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.fst (i ≫ f) (j ≫
      f)) hn (𝟙 _)
    ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j) hx
  have h12 : (ρ ≫ pullback.fst (amap L i j) j) ≫ amap L i j =
      ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j) ≫
        (L.mul f ⟨f ≫ ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.fst (i ≫ f) (j ≫ f)) ≫ i, by
            rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G,
                Category.id_comp _⟩).1 := by
    rw [h1, h2]
    apply mul_val_congr L hζq
    · simp only [Category.id_comp, Category.assoc]
    · rfl
  have hstab := hUstab ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.fst (i ≫ f) (j ≫ f)) hn
  rw [← hρpt]
  change ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j).base
      ((show Spec (CommRingCat.of k) from IsLocalRing.closedPoint k)) ∈
      (U : Set G) ↔ (ρ ≫ pullback.snd (amap L i j) j ≫ j).base ((show Spec (CommRingCat.of k) from
          IsLocalRing.closedPoint k)) ∈ (U : Set G)
  rw [hp2, h12, comp_base_apply _ (L.mul f _ _).1]
  constructor
  · intro hmem
    have hpre : ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j).base
        ((show Spec (CommRingCat.of k) from IsLocalRing.closedPoint k)) ∈
        (L.mul f ⟨f ≫ ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.fst (i ≫ f) (j ≫ f)) ≫ i, by
            rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G,
                Category.id_comp _⟩).1 ⁻¹ᵁ U := by
      rw [hstab]; exact hmem
    exact hpre
  · intro hmem
    have hpre : ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j).base
        ((show Spec (CommRingCat.of k) from IsLocalRing.closedPoint k)) ∈
        (L.mul f ⟨f ≫ ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.fst (i ≫ f) (j ≫ f)) ≫ i, by
            rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G,
                Category.id_comp _⟩).1 ⁻¹ᵁ U := hmem
    rw [hstab] at hpre
    exact hpre

end GroupLaw

end StableRelation

end AbelianVarieties.NOSProofs.StableSliceRelation

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u
open AbelianVarieties.NOSProofs.StableSliceRelation.StableRelation

theorem preimage_eq_preimage_and_isFinite_pullback_snd_action_slice_of_stable
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (_hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (S : Scheme.{u}) (j : S ⟶ G) [IsAffine S] [Nonempty S] [LocallyOfFiniteType (j ≫ f)]
    (hEt : Etale (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i))
    (U : G.Opens) (hUfin : IsFinite ((pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) ∣_ U))
    (hUstab : ∀ (n : Spec (CommRingCat.of k) ⟶ N) (hn : n ≫ i ≫ f = 𝟙 _),
      (L.mul f ⟨f ≫ n ≫ i, by
          rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G,
              Category.id_comp _⟩).1 ⁻¹ᵁ U = U) :
    (pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ (j ⁻¹ᵁ U) =
        (pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ⁻¹ᵁ (j ⁻¹ᵁ U) ∧
      IsFinite ((pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ∣_ (j ⁻¹ᵁ U)) := by
  have hFiniteLocal : IsZariskiLocalAtTarget
      (@IsFinite : MorphismProperty Scheme.{u}) := AlgebraicGeometry.isFiniteLocalAtTarget
  have : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    hFiniteLocal.toRespects
  exact ⟨preimage_fst_snd_eq_preimage_snd L i j hEt U hUstab,
    morphismRestrict_pullback_snd @IsFinite _ j U hUfin⟩

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_pullback_action_slice_mono_and_equivalence_of_preimage_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.SliceEquivalence

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace SliceRelation

open AbelianVarieties.NOSProofs.FiniteSliceLocus.FiniteLocus
  (amap mul_coe_congr ipt ipt_coe ipt_eq_comp pairNS pairNS_fst pairNS_snd
    comp_amap pairNS_amap ipt_mul ipt_injective ipt_one ipt_inv amap_over amap_over')

section Action

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f)) {S : Scheme.{u}} (j : S ⟶ G)

theorem comp_action {T : Scheme.{u}} (α : T ⟶ pullback (i ≫ f) f) (t : T ⟶ Spec (CommRingCat.of k))
    (ht : α ≫ pullback.fst _ _ ≫ i ≫ f = t) :
    α ≫ L.action i =
      (L.mul t (ipt i ⟨α ≫ pullback.fst _ _, ht⟩)
        ⟨α ≫ pullback.snd _ _, by rw [Category.assoc, ← pullback.condition]; exact ht⟩).1 := by
  have hz : α ≫ RelativeGroupLaw.actionSource f i = t := by
    change α ≫ pullback.snd (i ≫ f) f ≫ f = t
    rw [← pullback.condition]; exact ht
  rw [RelativeGroupLaw.action_def]
  have h1 := congrArg Subtype.val
    (L.mul_natural (RelativeGroupLaw.actionSource f i) t α hz (L.actionFstPoint i)
        (L.actionSndPoint i))
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h1
  rw [h1]
  apply mul_coe_congr L rfl
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.actionFstPoint_coe,
      ipt_coe,
      Category.assoc]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.actionSndPoint_coe]

variable (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))

include hi in
theorem pairNS_mul_amap {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (m n : SchemeHomOver t (i ≫ f))
    (s : T ⟶ S) (hs : s ≫ j ≫ f = t) :
    pairNS i j (LN.mul t m n) s hs ≫ amap L i j =
      (L.mul t (ipt i m) ⟨pairNS i j n s hs ≫ amap L i j, by
        rw [pairNS_amap]; exact (L.mul t _ _).2⟩).1 := by
  rw [pairNS_amap, ipt_mul L i LN hi, L.mul_assoc]
  apply mul_coe_congr L rfl _ _ _ _ rfl
  exact (pairNS_amap L i j n s hs).symm

omit hi in
theorem eq_pairNS {T : Scheme.{u}} (z : T ⟶ pullback (i ≫ f) (j ≫ f)) (t : T ⟶ Spec
    (CommRingCat.of k))
    (ht : z ≫ pullback.fst _ _ ≫ i ≫ f = t) :
    z = pairNS i j ⟨z ≫ pullback.fst _ _, ht⟩ (z ≫ pullback.snd _ _)
      (by rw [Category.assoc, ← pullback.condition]; exact ht) := by
  apply pullback.hom_ext
  · rw [pairNS_fst]
  · rw [pairNS_snd]

end Action

section Rel

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f))
  (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
  {S : Scheme.{u}} (j : S ⟶ G) (V : S.Opens)

/-- The first projection of the slice relation. -/
abbrev q₁ : pullback (amap L i j) j ⟶ S := pullback.fst (amap L i j) j ≫ pullback.snd (i ≫ f)
    (j ≫ f)
/-- The second projection of the slice relation. -/
abbrev q₂ : pullback (amap L i j) j ⟶ S := pullback.snd (amap L i j) j

variable (hV : q₁ L i j ⁻¹ᵁ V = q₂ L i j ⁻¹ᵁ V)

/-- The second projection restricted to the stable slice. -/
abbrev r₂ : (q₁ L i j ⁻¹ᵁ V).toScheme ⟶ V.toScheme :=
  ((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)

omit hi in
theorem r₁_ι : (q₁ L i j ∣_ V) ≫ V.ι = (q₁ L i j ⁻¹ᵁ V).ι ≫ q₁ L i j := morphismRestrict_ι _ _

omit hi in
theorem r₂_ι : r₂ L i j V hV ≫ V.ι = (q₁ L i j ⁻¹ᵁ V).ι ≫ q₂ L i j := by
  change (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)) ≫ V.ι = _
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.isoOfEq_hom_ι]

theorem rel_of_point {T : Scheme.{u}} (φ : T ⟶ (q₁ L i j ⁻¹ᵁ V).toScheme) (t : T ⟶ Spec
    (CommRingCat.of k))
    (ht : (φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j ≫ f = t) :
    ∃ (n : SchemeHomOver t (i ≫ f)),
      n.1 = ((φ ≫ (q₁ L i j ⁻¹ᵁ V).ι) ≫ pullback.fst (amap L i j) j) ≫ pullback.fst (i ≫ f) (j ≫
          f) ∧
      (L.mul t (ipt i n) ⟨(φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j, by
          rw [Category.assoc, Category.assoc]
          simpa only [Category.assoc] using ht⟩).1 =
        (φ ≫ r₂ L i j V hV) ≫ V.ι ≫ j := by
  have hs : (φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι = ((φ ≫ (q₁ L i j ⁻¹ᵁ V).ι) ≫ pullback.fst
      (amap L i j) j) ≫ pullback.snd (i ≫ f) (j ≫ f) := by
    rw [Category.assoc, r₁_ι]; simp only [Category.assoc]
  have hs' : (φ ≫ r₂ L i j V hV) ≫ V.ι = (φ ≫ (q₁ L i j ⁻¹ᵁ V).ι) ≫ pullback.snd (amap L i j) j :=
      by
    rw [Category.assoc, r₂_ι, Category.assoc]
  have htz : ((φ ≫ (q₁ L i j ⁻¹ᵁ V).ι) ≫ pullback.fst (amap L i j) j) ≫ pullback.fst _ _ ≫ i ≫
      f = t := by
    rw [pullback.condition, ← Category.assoc, ← hs, Category.assoc]; exact ht
  refine ⟨⟨((φ ≫ (q₁ L i j ⁻¹ᵁ V).ι) ≫ pullback.fst (amap L i j) j) ≫ pullback.fst (i ≫ f) (j ≫
      f), by rw [Category.assoc]; exact htz⟩, rfl, ?_⟩
  have e := comp_amap L i j ((φ ≫ (q₁ L i j ⁻¹ᵁ V).ι) ≫ pullback.fst (amap L i j) j) t htz
  rw [Category.assoc, pullback.condition, ← Category.assoc] at e
  rw [← Category.assoc (φ ≫ r₂ L i j V hV) V.ι j, hs']
  refine (mul_coe_congr L rfl _ _ _ _ rfl ?_).trans e.symm
  change (φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j = _
  rw [← Category.assoc, hs, Category.assoc]

theorem exists_point {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (n : SchemeHomOver t (i ≫
    f))
    (s s' : T ⟶ V.toScheme) (hs : (s ≫ V.ι) ≫ j ≫ f = t)
    (hrel : (L.mul t (ipt i n) ⟨(s ≫ V.ι) ≫ j,
        by rw [Category.assoc]; exact hs⟩).1 = (s' ≫ V.ι) ≫ j) :
    ∃ φ : T ⟶ (q₁ L i j ⁻¹ᵁ V).toScheme, φ ≫ (q₁ L i j ∣_ V) = s ∧ φ ≫ r₂ L i j V hV = s' := by
  let r : T ⟶ pullback (i ≫ f) (j ≫ f) := pairNS i j n (s ≫ V.ι) hs
  have hr : r ≫ amap L i j = (s' ≫ V.ι) ≫ j := by
    change pairNS i j n (s ≫ V.ι) hs ≫ amap L i j = _
    rw [pairNS_amap]; exact hrel
  let ρ : T ⟶ pullback (amap L i j) j := pullback.lift r (s' ≫ V.ι) hr
  have hρ₁ : ρ ≫ q₁ L i j = s ≫ V.ι := by
    change ρ ≫ pullback.fst _ _ ≫ pullback.snd _ _ = _
    rw [← Category.assoc, pullback.lift_fst]; exact pairNS_snd i j _ _ hs
  have hρ₂ : ρ ≫ q₂ L i j = s' ≫ V.ι := pullback.lift_snd _ _ _
  have hρV : Set.range ρ.base ⊆ Set.range (q₁ L i j ⁻¹ᵁ V).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change (ρ ≫ q₁ L i j).base z ∈ (V : Set ↥S)
    rw [hρ₁]
    change V.ι.base (s.base z) ∈ (V : Set ↥S)
    rw [← Scheme.Opens.range_ι V]; exact ⟨_, rfl⟩
  refine ⟨IsOpenImmersion.lift _ ρ hρV, ?_, ?_⟩
  · rw [← cancel_mono V.ι, Category.assoc, r₁_ι, ← Category.assoc, IsOpenImmersion.lift_fac, hρ₁]
  · rw [← cancel_mono V.ι, Category.assoc, r₂_ι, ← Category.assoc, IsOpenImmersion.lift_fac, hρ₂]

omit hi in
theorem eRS : q₁ L i j ≫ j ≫ f = q₂ L i j ≫ j ≫ f := by
  change (pullback.fst (amap L i j) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ≫ j ≫ f = pullback.snd
      (amap L i j) j ≫ j ≫ f
  rw [Category.assoc, ← amap_over, ← Category.assoc, pullback.condition, Category.assoc]

omit hi in
theorem legs_over {T : Scheme.{u}} (φ : T ⟶ (q₁ L i j ⁻¹ᵁ V).toScheme) :
    (φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j ≫ f = (φ ≫ r₂ L i j V hV) ≫ V.ι ≫ j ≫ f := by
  have l : (φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j ≫ f = φ ≫ (q₁ L i j ⁻¹ᵁ V).ι ≫ q₁ L i j ≫ j ≫ f := by
    rw [Category.assoc, ← Category.assoc (q₁ L i j ∣_ V) V.ι, r₁_ι, Category.assoc]
  have r : (φ ≫ r₂ L i j V hV) ≫ V.ι ≫ j ≫ f = φ ≫ (q₁ L i j ⁻¹ᵁ V).ι ≫ q₂ L i j ≫ j ≫ f := by
    rw [Category.assoc, ← Category.assoc (r₂ L i j V hV) V.ι, r₂_ι, Category.assoc]
  rw [l, r, eRS]

theorem mono [IsClosedImmersion i] {T : Scheme.{u}} (x y : T ⟶ (q₁ L i j ⁻¹ᵁ V).toScheme)
    (h₁ : x ≫ (q₁ L i j ∣_ V) = y ≫ (q₁ L i j ∣_ V)) (h₂ : x ≫ r₂ L i j V hV = y ≫
        r₂ L i j V hV) : x = y := by
  obtain ⟨t, ht⟩ : ∃ t : T ⟶ Spec (CommRingCat.of k), (x ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j ≫ f = t :=
      ⟨_, rfl⟩
  have ht' : (y ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j ≫ f = t := by rw [← h₁]; exact ht
  obtain ⟨nx, hnx, relx⟩ := rel_of_point L i j V hV x t ht
  obtain ⟨ny, hny, rely⟩ := rel_of_point L i j V hV y t ht'
  let : Group (SchemeHomOver t f) := L.pointGroup t
  have hj : (⟨(x ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j, by
          rw [Category.assoc, Category.assoc]
          simpa only [Category.assoc] using ht⟩ : SchemeHomOver t f) =
      ⟨(y ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j, by
          rw [Category.assoc, Category.assoc]
          simpa only [Category.assoc] using ht'⟩ :=
    Subtype.ext (by
      change (x ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j = (y ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j
      rw [h₁])
  have key : ipt i nx = ipt i ny := by
    have e : L.mul t (ipt i nx) ⟨(x ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j, by
          rw [Category.assoc, Category.assoc]
          simpa only [Category.assoc] using ht⟩ =
        L.mul t (ipt i ny) ⟨(y ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j, by
          rw [Category.assoc, Category.assoc]
          simpa only [Category.assoc] using ht'⟩ :=
      Subtype.ext (by rw [relx, rely, h₂])
    rw [hj] at e
    exact mul_right_cancel e
  have hn := congrArg Subtype.val (ipt_injective i _ _ key)
  rw [hnx, hny] at hn
  have h₁' : (x ≫ (q₁ L i j ∣_ V)) ≫ V.ι = (y ≫ (q₁ L i j ∣_ V)) ≫ V.ι := by rw [h₁]
  rw [Category.assoc, r₁_ι, Category.assoc, r₁_ι] at h₁'
  have h₂' : (x ≫ r₂ L i j V hV) ≫ V.ι = (y ≫ r₂ L i j V hV) ≫ V.ι := by rw [h₂]
  rw [Category.assoc, r₂_ι, Category.assoc, r₂_ι] at h₂'
  rw [← cancel_mono (q₁ L i j ⁻¹ᵁ V).ι]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using hn
    · simpa only [Category.assoc] using h₁'
  · simpa only [Category.assoc] using h₂'

include LN hi in
theorem equivalence (T : Scheme.{u}) :
    _root_.Equivalence fun x y : T ⟶ V.toScheme =>
      ∃ φ : T ⟶ (q₁ L i j ⁻¹ᵁ V).toScheme, φ ≫ (q₁ L i j ∣_ V) = x ∧ φ ≫ r₂ L i j V hV = y := by
  refine ⟨fun x => ?_, fun {x y} hxy => ?_, fun {x y z} hxy hyz => ?_⟩
  · obtain ⟨t, ht⟩ : ∃ t : T ⟶ Spec (CommRingCat.of k), (x ≫ V.ι) ≫ j ≫ f = t := ⟨_, rfl⟩
    refine exists_point L i j V hV t (LN.one t) x x ht ?_
    rw [ipt_one L i LN hi, L.one_mul]
  · obtain ⟨φ, rfl, rfl⟩ := hxy
    obtain ⟨t, ht⟩ : ∃ t : T ⟶ Spec (CommRingCat.of k),
        ((φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι) ≫ j ≫ f = t := ⟨_, rfl⟩
    obtain ⟨n, -, rel⟩ := rel_of_point L i j V hV φ t
        (by simpa only [Category.assoc] using ht)
    have ht' : ((φ ≫ r₂ L i j V hV) ≫ V.ι) ≫ j ≫ f = t := by
      rw [Category.assoc, ← legs_over L i j V hV φ]; simpa only [Category.assoc] using ht
    refine exists_point L i j V hV t (LN.inv t n) _ _ ht' ?_
    let : Group (SchemeHomOver t f) := L.pointGroup t
    rw [ipt_inv L i LN hi]
    have e : (⟨(φ ≫ r₂ L i j V hV) ≫ V.ι ≫ j, by
          rw [Category.assoc] at ht'
          rw [Category.assoc, Category.assoc]
          simpa only [Category.assoc] using ht'⟩ : SchemeHomOver t f) =
        L.mul t (ipt i n) ⟨(φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j, by
          rw [Category.assoc, Category.assoc]
          simpa only [Category.assoc] using ht⟩ :=
      Subtype.ext rel.symm
    have e2 : L.mul t (L.inv t (ipt i n)) ⟨((φ ≫ r₂ L i j V hV) ≫ V.ι) ≫ j,
        by rw [Category.assoc]; exact ht'⟩ =
        ⟨(φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j, by
          rw [Category.assoc, Category.assoc]
          simpa only [Category.assoc] using ht⟩ := by
      have : (⟨((φ ≫ r₂ L i j V hV) ≫ V.ι) ≫ j,
          by rw [Category.assoc]; exact ht'⟩ : SchemeHomOver t f) =
          ⟨(φ ≫ r₂ L i j V hV) ≫ V.ι ≫ j, by
          rw [Category.assoc] at ht'
          rw [Category.assoc, Category.assoc]
          simpa only [Category.assoc] using ht'⟩ :=
        Subtype.ext (Category.assoc _ _ _)
      rw [this, e]
      change (ipt i n)⁻¹ * (ipt i n * _) = _
      rw [inv_mul_cancel_left]
    rw [congrArg Subtype.val e2]
    exact Category.assoc _ _ _
  · obtain ⟨φ, rfl, rfl⟩ := hxy
    obtain ⟨ψ, hψ, rfl⟩ := hyz
    obtain ⟨t, ht⟩ : ∃ t : T ⟶ Spec (CommRingCat.of k),
        ((φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι) ≫ j ≫ f = t := ⟨_, rfl⟩
    obtain ⟨n, -, rel⟩ := rel_of_point L i j V hV φ t
        (by simpa only [Category.assoc] using ht)
    have htψ : (ψ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j ≫ f = t := by
      rw [hψ, ← legs_over L i j V hV φ]; simpa only [Category.assoc] using ht
    obtain ⟨n', -, rel'⟩ := rel_of_point L i j V hV ψ t htψ
    refine exists_point L i j V hV t (LN.mul t n' n) _ _
        (by simpa only [Category.assoc] using ht) ?_
    let : Group (SchemeHomOver t f) := L.pointGroup t
    rw [ipt_mul L i LN hi, L.mul_assoc]
    have e1 : L.mul t (ipt i n) ⟨(φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j, by
          rw [Category.assoc, Category.assoc]
          simpa only [Category.assoc] using ht⟩ =
        ⟨(ψ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j, by
          rw [Category.assoc, Category.assoc]
          simpa only [Category.assoc] using htψ⟩ := by
      apply Subtype.ext; rw [rel]; change (φ ≫ r₂ L i j V hV) ≫ V.ι ≫ j = (ψ ≫ (q₁ L i j ∣_ V)) ≫
          V.ι ≫ j; rw [hψ]
    have e0 : (⟨((φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι) ≫ j, by
          rw [Category.assoc]
          simpa only [Category.assoc] using ht⟩ : SchemeHomOver t f) =
        ⟨(φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j, by
          rw [Category.assoc, Category.assoc]
          simpa only [Category.assoc] using ht⟩ :=
      Subtype.ext (Category.assoc _ _ _)
    rw [e0, e1, rel']
    exact Category.assoc _ _ _

end Rel

end SliceRelation

end

end AbelianVarieties.NOSProofs.SliceEquivalence

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u
open AbelianVarieties.NOSProofs.SliceEquivalence.SliceRelation

theorem pullback_action_slice_mono_and_equivalence_of_preimage_eq
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (S : Scheme.{u}) (j : S ⟶ G) [IsAffine S] [Nonempty S] [LocallyOfFiniteType (j ≫ f)]
    (_hEt : Etale (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i))
    (V : S.Opens)
    (hV : (pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ V = (pullback.snd (pullback.map
              (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ⁻¹ᵁ V) :
    (∀ {T : Scheme.{u}} (x y : T ⟶ ((pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f
        (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ V).toScheme),
        x ≫ ((pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) = y ≫ ((pullback.fst
              (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) →
              x ≫ (((pullback (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j).isoOfEq hV).hom ≫ ((pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫
              f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ∣_ V)) = y ≫ (((pullback (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f
              (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j).isoOfEq hV).hom ≫ ((pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫
              f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ∣_ V)) → x = y) ∧
      (∀ T : Scheme.{u}, _root_.Equivalence fun x y : T ⟶ V.toScheme =>
        ∃ φ : T ⟶ ((pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ V).toScheme,
              φ ≫ ((pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) = x ∧
              φ ≫ (((pullback (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j).isoOfEq hV).hom ≫ ((pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫
              f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ∣_ V)) = y) := by
  refine ⟨fun x y h₁ h₂ => mono L i j V hV x y h₁ h₂,
      fun T => equivalence L i LN hi j V hV T⟩

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isFinite_flat_locallyOfFinitePresentation_pullback_action_slice_of_preimage_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem isFinite_flat_locallyOfFinitePresentation_pullback_action_slice_of_preimage_eq
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (S : Scheme.{u}) (j : S ⟶ G) [IsAffine S] [Nonempty S] [LocallyOfFiniteType (j ≫ f)]
    (hEt : Etale (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i))
    (V : S.Opens)
    (hV : (pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ V = (pullback.snd (pullback.map
              (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ⁻¹ᵁ V)
    (hfin : IsFinite ((pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ∣_ V)) :
    IsFinite ((pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) ∧
              Flat ((pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) ∧
              LocallyOfFinitePresentation ((pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫
              f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) ∧
      IsFinite (((pullback (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j).isoOfEq hV).hom ≫ ((pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫
              f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ∣_ V)) ∧ Flat (((pullback (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f
              (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j).isoOfEq hV).hom ≫ ((pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫
              f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ∣_ V)) ∧ LocallyOfFinitePresentation (((pullback (pullback.map (i ≫
              f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j).isoOfEq hV).hom ≫ ((pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫
              f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ∣_ V)) := by
  obtain ⟨σ, hσ₁, hσ₂⟩ :=
    exists_iso_pullback_action_slice_swap k f L g i LN h hi S j hEt
  revert hV
  generalize hφ : (pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f
      (𝟙 N) j (𝟙 _) ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
          L.action i) j ≫
      pullback.snd (i ≫ f) (j ≫ f)) = φ
  intro hV
  have hφ' : φ = σ.hom ≫ pullback.snd _ j := by rw [← hφ, hσ₁]
  subst hφ'
  have hfl : Flat (pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f
      (𝟙 N) j (𝟙 _) ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
          L.action i) j) :=
    inferInstance
  have hlfp : LocallyOfFinitePresentation (pullback.snd
      (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f
      (𝟙 N) j (𝟙 _) ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
          L.action i) j) :=
    inferInstance
  -- Give the restriction identity a fixed source before transporting finiteness.
  have hfiniteComp {X Y Z : Scheme.{u}} (e : X ≅ Y) (q : Y ⟶ Z) (U : Z.Opens)
      [IsFinite (q ∣_ U)] : IsFinite ((e.hom ≫ q) ∣_ U) := by
    have : IsIso (e.hom ∣_ q ⁻¹ᵁ U) := inferInstance
    have hcomp : IsFinite ((e.hom ∣_ q ⁻¹ᵁ U) ≫ (q ∣_ U)) := inferInstance
    exact (morphismRestrict_comp e.hom q U).symm ▸ hcomp
  refine ⟨hfiniteComp σ (pullback.snd _ j) V, ?_, ?_, ?_, ?_, ?_⟩
  all_goals infer_instance

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_base_mem_of_forall_isFinite_morphismRestrict_le_of_stable.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.NonemptyFiniteSlice

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace SliceNonempty

theorem ringHom_quasiFinite_of_etale {R S : Type u} [CommRing R] [CommRing S] {φ : R →+* S}
    (h : φ.Etale) : φ.QuasiFinite := by
  let : Algebra R S := φ.toAlgebra
  have : Algebra.Etale R S := h
  exact (inferInstance : Algebra.QuasiFinite R S)

open AbelianVarieties.NOSProofs.StableSliceRelation.StableRelation
  (comp_base_apply mul_val_congr comp_translation comp_action)

theorem locallyQuasiFinite_of_etale {X Y : Scheme.{u}} (a : X ⟶ Y) [Etale a] :
    LocallyQuasiFinite a := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  exact ringHom_quasiFinite_of_etale (HasRingHomProperty.appLE @Etale a inferInstance U V e)

theorem exists_isOpen_irreducible_subset {α : Type u} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α]
    {O : Set α} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ W : Set α, IsOpen W ∧ W.Nonempty ∧ IsIrreducible W ∧ W ⊆ O := by
  have : Nonempty O := hne.to_subtype
  obtain ⟨o, ho, hone, hoZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (irreducibleComponent (Classical.arbitrary O))
          (irreducibleComponent_mem_irreducibleComponents _)
  refine ⟨Subtype.val '' o, hO.isOpenMap_subtype_val o ho, hone.image _, ?_, ?_⟩
  · refine IsIrreducible.image ?_ Subtype.val continuous_subtype_val.continuousOn
    exact ⟨hone, (isIrreducible_irreducibleComponent.2).open_subset ho hoZ⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2

end SliceNonempty

end AbelianVarieties.NOSProofs.NonemptyFiniteSlice

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u
open AbelianVarieties.NOSProofs.NonemptyFiniteSlice.SliceNonempty
open AbelianVarieties.NOSProofs.StableSliceRelation.StableRelation
  (comp_base_apply mul_val_congr comp_translation comp_action)

theorem exists_base_mem_of_forall_isFinite_morphismRestrict_le_of_stable
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (_hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (S : Scheme.{u}) (j : S ⟶ G) [IsAffine S] [Nonempty S] [LocallyOfFiniteType (j ≫ f)]
    (hEt : Etale (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i))
    (U : G.Opens) (hU : ∀ W : G.Opens, IsFinite ((pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f
        (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) ∣_ W) → W ≤ U)
    (hUstab : ∀ (n : Spec (CommRingCat.of k) ⟶ N) (hn : n ≫ i ≫ f = 𝟙 _),
      (L.mul f ⟨f ≫ n ≫ i, by
          rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G,
              Category.id_comp _⟩).1 ⁻¹ᵁ U = U) :
    ∃ s : S, j.base s ∈ U := by
  have hFiniteLocal : IsZariskiLocalAtTarget
      (@IsFinite : MorphismProperty Scheme.{u}) := AlgebraicGeometry.isFiniteLocalAtTarget
  have : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    hFiniteLocal.toRespects
  have : Smooth f := SmoothOfRelativeDimension.smooth g f
  have haf : (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) ≫ f =
      pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f := by
    rw [Category.assoc, L.action_over, RelativeGroupLaw.actionSource, ← Category.assoc,
      pullback.lift_snd, Category.assoc]
  have : LocallyOfFiniteType (pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f) := inferInstance
  have hsep : IsSeparated (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) := by
    have : IsSeparated ((pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) ≫ f) := by rw [haf]; infer_instance
    exact IsSeparated.of_comp _ f
  have hqc : QuasiCompact (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) := by
    have : QuasiCompact ((pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) ≫ f) := by rw [haf]; infer_instance
    exact QuasiCompact.of_comp _ f
  have hlqf : LocallyQuasiFinite (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) := locallyQuasiFinite_of_etale _
  have key : ∀ z : ↥(pullback (i ≫ f) (j ≫ f)), IsClosed {z} →
      ((pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i)).base z ∈ U → ∃ s : S, j.base s ∈ U := by
    intro z hz hzU
    set ζ := pointOfClosedPoint (pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f) z hz with hζ
    have hζq : ζ ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f = 𝟙 _ :=
      pointOfClosedPoint_comp _ z hz
    have hn : (ζ ≫ pullback.fst (i ≫ f) (j ≫ f)) ≫ i ≫ f = 𝟙 _ := by
      rw [Category.assoc, pullback.condition]; exact hζq
    have hx : (ζ ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j) ≫ f = 𝟙 _ := by
      simpa only [Category.assoc] using hζq
    have h1 := comp_action L i j ζ
    have h2 := comp_translation L i (ζ ≫ pullback.fst (i ≫ f) (j ≫ f)) hn (𝟙 _)
      (ζ ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j) hx
    have h12 : ζ ≫ (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) =
        (ζ ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j) ≫
          (L.mul f ⟨f ≫ (ζ ≫ pullback.fst (i ≫ f) (j ≫ f)) ≫ i, by
          rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G,
              Category.id_comp _⟩).1 := by
      rw [h1, h2]
      apply mul_val_congr L hζq
      · simp only [Category.id_comp, Category.assoc]
      · rfl
    have hζpt : ζ.base ((show Spec (CommRingCat.of k) from IsLocalRing.closedPoint k)) = z :=
        pointOfClosedPoint_apply _ z hz _
    have hmem : ((L.mul f ⟨f ≫ (ζ ≫ pullback.fst (i ≫ f) (j ≫ f)) ≫ i, by
          rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G,
              Category.id_comp _⟩).1).base
        ((ζ ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j).base ((show Spec (CommRingCat.of k) from
            IsLocalRing.closedPoint k))) ∈ U := by
      rw [← comp_base_apply, ← h12, comp_base_apply, hζpt]
      exact hzU
    have hstab := hUstab (ζ ≫ pullback.fst (i ≫ f) (j ≫ f)) hn
    have hpre : (ζ ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j).base ((show Spec (CommRingCat.of k) from
        IsLocalRing.closedPoint k)) ∈
        (L.mul f ⟨f ≫ (ζ ≫ pullback.fst (i ≫ f) (j ≫ f)) ≫ i, by
          rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G,
              Category.id_comp _⟩).1 ⁻¹ᵁ U := hmem
    rw [hstab] at hpre
    refine ⟨(pullback.snd (i ≫ f) (j ≫ f)).base (ζ.base ((show Spec (CommRingCat.of k) from
        IsLocalRing.closedPoint k))), ?_⟩
    exact hpre
  have hopen : IsOpenMap ((pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i)).base := Scheme.Hom.isOpenMap _
  obtain ⟨e⟩ : Nonempty (Spec (CommRingCat.of k) ⟶ N) := ⟨(LN.one (𝟙 _)).1⟩
  have hNS : Nonempty ↥(pullback (i ≫ f) (j ≫ f)) := by
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i ≫ f) (g := j ≫ f)
      (e.base ((show Spec (CommRingCat.of k) from
          IsLocalRing.closedPoint k))) (Classical.arbitrary S) (Subsingleton.elim _ _)
    exact ⟨z⟩
  have : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian G := {}
  have : TopologicalSpace.NoetherianSpace G := inferInstance
  obtain ⟨W, hWo, hWne, hWirr, hWIm⟩ := exists_isOpen_irreducible_subset (α := G)
    hopen.isOpen_range (Set.range_nonempty _)
  let Y₁ : G.Opens := ⟨W, hWo⟩
  have : IrreducibleSpace Y₁.toScheme := isIrreducible_iff_irreducibleSpace.mp hWirr
  obtain ⟨U₁, hU₁ne, hU₁fin⟩ :=
    AlgebraicGeometry.LocallyQuasiFinite.exists_isFinite_morphismRestrict_of_irreducibleSpace
      ((pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) ∣_ Y₁)
  have hW₁fin : IsFinite ((pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) ∣_ (Y₁.ι ''ᵁ U₁)) :=
    (MorphismProperty.arrow_mk_iso_iff @IsFinite (morphismRestrictRestrict _ Y₁ U₁)).1 hU₁fin
  have hW₁U : Y₁.ι ''ᵁ U₁ ≤ U := hU _ hW₁fin
  obtain ⟨u₁, hu₁⟩ := hU₁ne
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, ((pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i)).base z₀ = Y₁.ι.base u₁ := hWIm u₁.2
  have : JacobsonSpace ↥(pullback (i ≫ f) (j ≫ f)) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f)
  have hz₀mem : z₀ ∈ (((pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i)) ⁻¹ᵁ (Y₁.ι ''ᵁ U₁) : Set _) := by
    change ((pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i)).base z₀ ∈ Y₁.ι ''ᵁ U₁
    rw [hz₀]; exact ⟨u₁, hu₁, rfl⟩
  obtain ⟨z, hzW, hzcl⟩ := nonempty_inter_closedPoints ⟨z₀, hz₀mem⟩
    (((pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i)) ⁻¹ᵁ (Y₁.ι ''ᵁ U₁)).2.isLocallyClosed
  exact key z hzcl (hW₁U hzW)

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_finiteLocallyFree_sliceRelation_of_etale.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem exists_opens_saturated_finiteLocallyFree_sliceRelation_of_etale
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (S : Scheme.{u}) (j : S ⟶ G) [IsAffine S] [Nonempty S] [LocallyOfFiniteType (j ≫ f)]
    (hEt : Etale (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i)) :
    ∃ (V : S.Opens) (hV : (pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ V = (pullback.snd (pullback.map
              (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ⁻¹ᵁ V),
      Nonempty (V.toScheme) ∧
      IsFinite ((pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) ∧
              Flat ((pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) ∧
              LocallyOfFinitePresentation ((pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫
              f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) ∧
      IsFinite (((pullback (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j).isoOfEq hV).hom ≫ ((pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫
              f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ∣_ V)) ∧ Flat (((pullback (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f
              (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j).isoOfEq hV).hom ≫ ((pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫
              f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ∣_ V)) ∧ LocallyOfFinitePresentation (((pullback (pullback.map (i ≫
              f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j).isoOfEq hV).hom ≫ ((pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫
              f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ∣_ V)) ∧
      (∀ {T : Scheme.{u}} (x y : T ⟶ ((pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f
          (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ V).toScheme),
        x ≫ ((pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) = y ≫ ((pullback.fst
              (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) →
              x ≫ (((pullback (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j).isoOfEq hV).hom ≫ ((pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫
              f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ∣_ V)) = y ≫ (((pullback (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f
              (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j).isoOfEq hV).hom ≫ ((pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫
              f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ∣_ V)) → x = y) ∧
      (∀ T : Scheme.{u}, _root_.Equivalence fun x y : T ⟶ V.toScheme =>
        ∃ φ : T ⟶ ((pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ V).toScheme,
              φ ≫ ((pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) = x ∧
              φ ≫ (((pullback (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j).isoOfEq hV).hom ≫ ((pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫
              f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ∣_ V)) = y) ∧
      (∀ x : V.toScheme, ∃ U : (V.toScheme).Opens, IsAffineOpen U ∧
        ∀ r : ((pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ V).toScheme,
              ((pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ∣_ V).base r = x →
              (((pullback (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j).isoOfEq hV).hom ≫ ((pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫
              f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ∣_ V)).base r ∈ U) := by
  obtain ⟨U, hUfin, hUmax, hUstab⟩ :=
    exists_opens_isFinite_morphismRestrict_action_slice_maximal_stable
      k f L g i LN h hi S j hEt
  obtain ⟨s, hs⟩ :=
    exists_base_mem_of_forall_isFinite_morphismRestrict_le_of_stable
      k f L g i LN h hi S j hEt U hUmax hUstab
  obtain ⟨hV, hfin⟩ :=
    preimage_eq_preimage_and_isFinite_pullback_snd_action_slice_of_stable
      k f L g i LN h hi S j hEt U hUfin hUstab
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
    isFinite_flat_locallyOfFinitePresentation_pullback_action_slice_of_preimage_eq
      k f L g i LN h hi S j hEt (j ⁻¹ᵁ U) hV hfin
  obtain ⟨hmono, hequiv⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.pullback_action_slice_mono_and_equivalence_of_preimage_eq
      k f L g i LN h hi S j hEt (j ⁻¹ᵁ U) hV
  refine ⟨j ⁻¹ᵁ U, hV, ⟨⟨s, hs⟩⟩, h₁, h₂, h₃, h₄, h₅, h₆, hmono, hequiv, ?_⟩
  intro x
  obtain ⟨W, hW, hFW⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_subset_of_finite_of_isAffine (X := S) (j ⁻¹ᵁ U)
      ((fun r => (((pullback (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j).isoOfEq hV).hom ≫ ((pullback.snd (pullback.map (i ≫ f) (j ≫ f) (i ≫
              f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j) ∣_ (j ⁻¹ᵁ U))).base r) ''
        (((pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ∣_ (j ⁻¹ᵁ U)).base ⁻¹' {x}))
      ((((pullback.fst (pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
              L.action i) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ∣_
              (j ⁻¹ᵁ U)).finite_preimage_singleton x).image _)
  exact ⟨W, hW, fun r hr => hFW ⟨r, hr, rfl⟩⟩

end GoodReductionJacobian.RelativeGroupLaw
end
