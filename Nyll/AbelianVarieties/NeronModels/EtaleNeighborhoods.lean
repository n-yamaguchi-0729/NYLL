/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Tactic.Choose
public import Nyll.AbelianVarieties.NeronModels.Density
public import Nyll.AbelianVarieties.NeronModels.Multiplication
public import Nyll.AbelianVarieties.NeronModels.Translates
public import Nyll.SchemeTheory.LocalGeometry.DVRLifts
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.SchemeTheory.Morphisms.SmoothReducedReduced
public import Nyll.SchemeTheory.RingTheory.Henselian.ModuleFinite

/-! # Finite étale neighborhoods extending a partial group law -/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_opens_forall_mem_of_mem_range_of_forall_exists_translation_of_henselianLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.EtaleTranslationDomains


noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian Topology

universe u v

namespace TranslationDomains

open AbelianVarieties.NOSProofs.DensityBaseChange.FibreDensity
  (dense_fibre_iff dense_preimage_of_isPullback dense_fibre_of_isPullback)

section General

scoped instance subsingleton_spec_residueField (Y : Scheme.{u}) (x : Y) :
    Subsingleton ↥(Spec (Y.residueField x)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum (Y.residueField x)))

theorem dense_of_forall_dense_fibre {X Z : Type*} [TopologicalSpace X] (p : X → Z) (S : Set X)
    (h : ∀ z : Z, Dense ((Subtype.val : {x : X // p x = z} → X) ⁻¹' S)) : Dense S := by
  intro x
  have hx : (⟨x, rfl⟩ : {x' : X // p x' = p x}) ∈
      closure ((Subtype.val : {x' : X // p x' = p x} → X) ⁻¹' S) := h (p x) ⟨x, rfl⟩
  rw [closure_subtype] at hx
  exact closure_mono (Set.image_preimage_subset _ _) hx

theorem subset_closure_inter {X : Type*} [TopologicalSpace X] {O A A' : Set X} (hO : IsOpen O)
    (hA : IsOpen A) (h : O ⊆ closure A) (h' : O ⊆ closure A') : O ⊆ closure (A ∩ A') := by
  intro o ho
  rw [mem_closure_iff]
  intro N hN hoN
  obtain ⟨a₁, ⟨ha₁N, ha₁O⟩, ha₁A⟩ : (N ∩ O ∩ A).Nonempty :=
    mem_closure_iff.mp (h ho) (N ∩ O) (hN.inter hO) ⟨hoN, ho⟩
  obtain ⟨a₂, ⟨⟨ha₂N, -⟩, ha₂A⟩, ha₂A'⟩ : (N ∩ O ∩ A ∩ A').Nonempty :=
    mem_closure_iff.mp (h' ha₁O) (N ∩ O ∩ A) ((hN.inter hO).inter hA) ⟨⟨ha₁N, ha₁O⟩, ha₁A⟩
  exact ⟨a₂, ha₂N, ha₂A, ha₂A'⟩

theorem eq_of_comp_ι_eq {X Z S : Scheme.{u}} [IsReduced X] (s : Z ⟶ S) [IsSeparated s]
    {f g : X ⟶ Z} (hs : f ≫ s = g ≫ s) (W : X.Opens) (hW : Dense (W : Set X)) (h : W.ι ≫ f = W.ι
      ≫ g) :
    f = g := by
  have : IsDominant W.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact hW⟩
  exact ext_of_isDominant_of_isSeparated s hs W.ι h

theorem exists_glue_of_isOpenImmersion {X Z S : Scheme.{u}} [IsReduced X] (p : X ⟶ S) (s : Z ⟶ S)
    [IsSeparated s] {I : Type v} (F : I → Scheme.{u}) (j : ∀ i, F i ⟶ X) [∀ i, IsOpenImmersion
      (j i)]
    (hcov : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (g : ∀ i, F i ⟶ Z) (hg : ∀ i, g i ≫ s = j i ≫ p)
    (hagree : ∀ i i', ∃ W : Set X, IsOpen W ∧ Set.range (j i) ∩ Set.range (j i') ⊆ closure W ∧
      ∀ {T : Scheme.{u}} (t₁ : T ⟶ F i) (t₂ : T ⟶ F i'), t₁ ≫ j i = t₂ ≫ j i' →
        Set.range (t₁ ≫ j i) ⊆ W → t₁ ≫ g i = t₂ ≫ g i') :
    ∃ G : X ⟶ Z, (∀ i, j i ≫ G = g i) ∧ G ≫ s = p := by
  let 𝒰 : Scheme.OpenCover.{v} X := Scheme.Cover.mkOfCovers I F j
    (fun x => by obtain ⟨i, z, hz⟩ := hcov x; exact ⟨i, z, hz⟩) inferInstance
  have hcompat : ∀ i i', pullback.fst (j i) (j i') ≫ g i =
      pullback.snd (j i) (j i') ≫ g i' := by
    intro i i'
    obtain ⟨W, hWo, hcl, hW⟩ := hagree i i'
    have hi : IsOpenImmersion (j i) := inferInstance
    have hi' : IsOpenImmersion (j i') := inferInstance
    have : IsOpenImmersion (pullback.fst (j i) (j i')) :=
      MorphismProperty.pullback_fst
        (P := (@IsOpenImmersion : MorphismProperty Scheme.{u})) (j i) (j i') hi'
    have : IsReduced (pullback (j i) (j i')) :=
      isReduced_of_isOpenImmersion (pullback.fst (j i) (j i') ≫ j i)
    let e : pullback (j i) (j i') ⟶ X := pullback.fst (j i) (j i') ≫ j i
    let W' : (pullback (j i) (j i')).Opens := ⟨e ⁻¹' W, hWo.preimage e.continuous⟩
    have hmem : ∀ n, e n ∈ Set.range (j i) ∩ Set.range (j i') := fun n =>
      ⟨⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩,
        ⟨pullback.snd (j i) (j i') n, by rw [← Scheme.Hom.comp_apply, ← pullback.condition]⟩⟩
    have hW'd : Dense (W' : Set ↥(pullback (j i) (j i'))) := by
      rw [dense_iff_inter_open]
      rintro N hN ⟨n₀, hn₀⟩
      have he : IsOpenEmbedding e := e.isOpenEmbedding
      obtain ⟨_, ⟨⟨n, hn, rfl⟩, hnW⟩⟩ : (e '' N ∩ W).Nonempty :=
        mem_closure_iff.mp (hcl (hmem n₀)) (e '' N) (he.isOpenMap _ hN) ⟨n₀, hn₀, rfl⟩
      exact ⟨n, hn, hnW⟩
    refine eq_of_comp_ι_eq s ?_ W' hW'd ?_
    · rw [Category.assoc, Category.assoc, hg, hg, pullback.condition_assoc]
    · rw [← Category.assoc, ← Category.assoc]
      refine hW (W'.ι ≫ pullback.fst _ _) (W'.ι ≫ pullback.snd _ _)
        (by rw [Category.assoc, Category.assoc, pullback.condition]) ?_
      rintro _ ⟨w, rfl⟩
      change (W'.ι ≫ e) w ∈ W
      exact w.2
  refine ⟨𝒰.glueMorphisms g hcompat, fun i => 𝒰.ι_glueMorphisms g hcompat i, ?_⟩
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun i => ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ s) (𝒰.ι_glueMorphisms g hcompat i)).trans (hg i))

end General

section Setup

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)

/-- The partial translation map keeping the first coordinate. -/
abbrev Phi : (U : Scheme.{u}) ⟶ pullback y y :=
  open AbelianVarieties.NOSProofs in
  EtaleTranslationPieces.TranslationPiece.Phi y U m

/-- The partial translation map keeping the second coordinate. -/
abbrev Psi : (U : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
    (m.2.trans (by rw [Category.assoc, pullback.condition]))

/-- Base change of the second projection along a chosen point. -/
def lamSnd {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Y) (hg : g ≫ y = c) :
    pullback y c ⟶ pullback y y :=
  pullback.lift (pullback.fst y c) (pullback.snd y c ≫ g) (by rw [Category.assoc, hg,
    pullback.condition])

@[reassoc]
theorem lamSnd_fst {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Y) (hg : g ≫ y =
  c) :
    lamSnd y c g hg ≫ pullback.fst y y = pullback.fst y c := pullback.lift_fst _ _ _

@[reassoc]
theorem lamSnd_snd {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Y) (hg : g ≫ y =
  c) :
    lamSnd y c g hg ≫ pullback.snd y y = pullback.snd y c ≫ g := pullback.lift_snd _ _ _

theorem isPullback_lamSnd {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Y)
    (hg : g ≫ y = c) : IsPullback (pullback.snd y c) (lamSnd y c g hg) g (pullback.snd y y) := by
  refine IsPullback.of_bot (v₂₁ := pullback.fst y y) (v₂₂ := y) (h₃₁ := y) ?_ (lamSnd_snd y c g
    hg).symm
    (IsPullback.of_hasPullback y y).flip
  rw [lamSnd_fst, hg]
  exact (IsPullback.of_hasPullback y c).flip

/-- Base change of the first projection along a chosen point. -/
def lamFst {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Y) (hg : g ≫ y = c) :
    pullback y c ⟶ pullback y y :=
  open AbelianVarieties.NOSProofs in
  EtaleTranslationPieces.TranslationPiece.lamFst y c g hg

@[reassoc]
theorem lamFst_fst {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Y) (hg : g ≫ y =
  c) :
    lamFst y c g hg ≫ pullback.fst y y = pullback.snd y c ≫ g :=
  open AbelianVarieties.NOSProofs in
  EtaleTranslationPieces.TranslationPiece.lamFst_fst y c g hg

@[reassoc]
theorem lamFst_snd {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Y) (hg : g ≫ y =
  c) :
    lamFst y c g hg ≫ pullback.snd y y = pullback.fst y c :=
  open AbelianVarieties.NOSProofs in
  EtaleTranslationPieces.TranslationPiece.lamFst_snd y c g hg

theorem isPullback_lamFst {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Y)
    (hg : g ≫ y = c) : IsPullback (pullback.snd y c) (lamFst y c g hg) g (pullback.fst y y) :=
  open AbelianVarieties.NOSProofs in
  EtaleTranslationPieces.TranslationPiece.isPullback_lamFst y c g hg

end Setup

section Level

/-- The spectrum morphism induced by a base algebra. -/
abbrev bS (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  open AbelianVarieties.NOSProofs in
  EtaleTranslationPieces.TranslationPiece.bS A B

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (R' : Type u) [CommRing R'] [Algebra R R']

/-- The model after the finite étale base extension. -/
abbrev Y1 : Scheme.{u} :=
  open AbelianVarieties.NOSProofs in
  EtaleTranslationPieces.TranslationPiece.Y1 y R'

/-- The structure morphism after base extension. -/
abbrev y1 : Y1 y R' ⟶ Spec (CommRingCat.of R') :=
  open AbelianVarieties.NOSProofs in
  EtaleTranslationPieces.TranslationPiece.y1 y R'

/-- The projection to the original model. -/
abbrev p1 : Y1 y R' ⟶ Y :=
  open AbelianVarieties.NOSProofs in
  EtaleTranslationPieces.TranslationPiece.p1 y R'

/-- The pair of base-changed model points. -/
abbrev P1 : Scheme.{u} :=
  open AbelianVarieties.NOSProofs in
  EtaleTranslationPieces.TranslationPiece.P1 y R'

/-- The induced projection on pairs of model points. -/
def pi1 : P1 y R' ⟶ pullback y y :=
  open AbelianVarieties.NOSProofs in
  EtaleTranslationPieces.TranslationPiece.pi1 y R'

@[reassoc (attr := simp)]
theorem pi1_fst : pi1 y R' ≫ pullback.fst y y = pullback.fst _ _ ≫ p1 y R' :=
  open AbelianVarieties.NOSProofs in
  EtaleTranslationPieces.TranslationPiece.pi1_fst y R'

@[reassoc (attr := simp)]
theorem pi1_snd : pi1 y R' ≫ pullback.snd y y = pullback.snd _ _ ≫ p1 y R' :=
  open AbelianVarieties.NOSProofs in
  EtaleTranslationPieces.TranslationPiece.pi1_snd y R'

theorem isPullback_pi1_fst :
    IsPullback (pi1 y R') (pullback.fst (y1 y R') (y1 y R')) (pullback.fst y y) (p1 y R') :=
  open AbelianVarieties.NOSProofs in
  EtaleTranslationPieces.TranslationPiece.isPullback_pi1_fst y R'

end Level

/-- The partial action and a finite étale extension used in the gluing construction. -/
structure Cx where
  /-- The discrete valuation base ring. -/
  R : Type u
  /-- The commutative ring structure on the base. -/
  [instR : CommRing R]
  /-- The base is a domain. -/
  [dom : IsDomain R]
  /-- The base is a discrete valuation ring. -/
  [dvr : IsDiscreteValuationRing R]
  /-- The base satisfies Hensel lifting. -/
  [hens : HenselianLocalRing R]
  /-- The original model. -/
  Y : Scheme.{u}
  /-- Its structure morphism. -/
  y : Y ⟶ Spec (CommRingCat.of R)
  /-- Smoothness of the original model. -/
  [smooth : Smooth y]
  /-- The domain of partial multiplication. -/
  U : (pullback y y).Opens
  /-- The partial multiplication morphism. -/
  m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y
  /-- Density along the first projection. -/
  hU₁ : ∀ x : Y,
    Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y
      y)) ⁻¹'
        (U : Set ↑(pullback y y)))
  /-- Density along the second projection. -/
  hU₂ : ∀ x : Y,
    Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y
      y)) ⁻¹'
        (U : Set ↑(pullback y y)))
  /-- The first translation map is an open immersion. -/
  hΦ : IsOpenImmersion (Phi y U m)
  /-- Density of the first translation image along the second projection. -/
  hΦ₂ : ∀ x : Y,
    Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y
      y)) ⁻¹'
        (Set.range (Phi y U m).base))
  /-- The second translation map is an open immersion. -/
  hΨ : IsOpenImmersion (Psi y U m)
  /-- Associativity on the common domain. -/
  hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
    u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
    p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫
      pullback.snd y y →
    q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y =
      v.1 ≫ m.1 →
    p.1 ≫ m.1 = q.1 ≫ m.1
  /-- The generic fiber is contained in the multiplication domain. -/
  hUK : ∀ q : ↑(pullback y y), (pullback.fst y y ≫ y).base q ≠ IsLocalRing.closedPoint R → q ∈ U
  /-- The finite étale extension ring. -/
  R' : Type u
  /-- Its commutative ring structure. -/
  [instR' : CommRing R']
  /-- The extension ring is a domain. -/
  [dom' : IsDomain R']
  /-- The extension ring is a discrete valuation ring. -/
  [dvr' : IsDiscreteValuationRing R']
  /-- The algebra structure of the base extension. -/
  [alg : Algebra R R']
  /-- The base extension is finite as a module. -/
  [fin : Module.Finite R R']
  /-- The base extension is étale. -/
  [et : Algebra.Etale R R']
  /-- The base extension is faithfully flat. -/
  [ff : Module.FaithfullyFlat R R']
  /-- The refined model. -/
  Y' : Scheme.{u}
  /-- The structure morphism of the refined model. -/
  y' : Y' ⟶ Spec (CommRingCat.of R')
  /-- The refined model is smooth. -/
  [smooth' : Smooth y']
  /-- The refined model is separated. -/
  [sep' : IsSeparated y']
  /-- The inclusion of the base-changed original model. -/
  ι : SchemeHomOver (y1 y R') y'
  /-- The inclusion is an open immersion. -/
  [oi : IsOpenImmersion ι.1]
  /-- The refined domain of partial multiplication. -/
  U' : (pullback y' y').Opens
  /-- The refined partial multiplication. -/
  m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y'
  /-- Compatibility with the original partial multiplication. -/
  hext : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
      (w : SchemeHomOver (t' ≫ bS R R') (U.ι ≫ pullback.fst y y ≫ y))
      (a b c : SchemeHomOver (t' ≫ bS R R') y),
    a.1 = w.1 ≫ U.ι ≫ pullback.fst y y → b.1 = w.1 ≫ U.ι ≫ pullback.snd y y → c.1 = w.1 ≫ m.1 →
    ∃ w' : SchemeHomOver t' (U'.ι ≫ pullback.fst y' y' ≫ y'),
      w'.1 ≫ U'.ι ≫ pullback.fst y' y' = (RelativeGroupLaw.baseChangePointOfBase (bS R R') a).1
        ≫ ι.1 ∧
      w'.1 ≫ U'.ι ≫ pullback.snd y' y' = (RelativeGroupLaw.baseChangePointOfBase (bS R R') b).1
        ≫ ι.1 ∧
      w'.1 ≫ m'.1 = (RelativeGroupLaw.baseChangePointOfBase (bS R R') c).1 ≫ ι.1
  /-- Compatible translations after each further finite étale extension. -/
  hstat : ∀ (R'' : Type u) (_ : CommRing R'') (_ : IsDomain R'') (_ : IsDiscreteValuationRing R'')
      (_ : Algebra R' R'') (_ : Module.Finite R' R'') (_ : Algebra.Etale R' R'') (_ :
        Module.FaithfullyFlat R' R'')
      (a : Spec (CommRingCat.of R'') ⟶ Y),
    a ≫ y = bS R' R'' ≫ bS R R' →
    ∃ τ : pullback y (bS R' R'' ≫ bS R R') ⟶ pullback y' (bS R' R''),
      τ ≫ pullback.snd y' (bS R' R'') = pullback.snd y (bS R' R'' ≫ bS R R') ∧
      ∀ {T : Scheme.{u}} (x : T ⟶ pullback y (bS R' R'' ≫ bS R R')) (w : T ⟶ (U : Scheme.{u}))
        (v : T ⟶ pullback y (bS R R')),
        w ≫ U.ι ≫ pullback.fst y y = x ≫ pullback.snd y (bS R' R'' ≫ bS R R') ≫ a →
        w ≫ U.ι ≫ pullback.snd y y = x ≫ pullback.fst y (bS R' R'' ≫ bS R R') →
        v ≫ pullback.fst y (bS R R') = w ≫ m.1 →
        v ≫ pullback.snd y (bS R R') = x ≫ pullback.snd y (bS R' R'' ≫ bS R R') ≫ bS R' R'' →
        x ≫ τ ≫ pullback.fst y' (bS R' R'') = v ≫ ι.1

attribute [local instance] Cx.instR Cx.dom Cx.dvr Cx.hens Cx.smooth
  Cx.instR' Cx.dom' Cx.dvr' Cx.alg Cx.fin Cx.et Cx.ff Cx.smooth' Cx.sep' Cx.oi

namespace Cx

variable (C : Cx.{u})

/-- The pair scheme for the extended model. -/
abbrev P : Scheme.{u} := P1 C.y C.R'

/-- The pulled-back domain of partial multiplication. -/
abbrev U₁ : C.P.Opens := pi1 C.y C.R' ⁻¹ᵁ C.U

/-- The projection from the pulled-back multiplication domain. -/
abbrev πU : (C.U₁ : Scheme.{u}) ⟶ C.U := pi1 C.y C.R' ∣_ C.U

@[reassoc]
theorem πU_ι : C.πU ≫ C.U.ι = C.U₁.ι ≫ pi1 C.y C.R' := morphismRestrict_ι _ _

@[reassoc]
theorem πU_fst : C.πU ≫ C.U.ι ≫ pullback.fst C.y C.y = C.U₁.ι ≫ pullback.fst _ _ ≫ p1 C.y C.R'
  := by
  rw [πU_ι_assoc, pi1_fst]

@[reassoc]
theorem πU_snd : C.πU ≫ C.U.ι ≫ pullback.snd C.y C.y = C.U₁.ι ≫ pullback.snd _ _ ≫ p1 C.y C.R'
  := by
  rw [πU_ι_assoc, pi1_snd]

/-- Multiplication lifted to the base-changed model. -/
def m₁ : (C.U₁ : Scheme.{u}) ⟶ Y1 C.y C.R' :=
  pullback.lift (C.πU ≫ C.m.1) (C.U₁.ι ≫ pullback.fst _ _ ≫ y1 C.y C.R') (by
    rw [Category.assoc, C.m.2, πU_fst_assoc, Category.assoc, Category.assoc, ← pullback.condition])

@[reassoc (attr := simp)]
theorem m₁_p1 : C.m₁ ≫ p1 C.y C.R' = C.πU ≫ C.m.1 := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem m₁_y1 : C.m₁ ≫ y1 C.y C.R' = C.U₁.ι ≫ pullback.fst _ _ ≫ y1 C.y C.R' :=
  pullback.lift_snd _ _ _

/-- The known multiplication map on its original domain. -/
def G₀ : (C.U₁ : Scheme.{u}) ⟶ C.Y' := C.m₁ ≫ C.ι.1

theorem G₀_y' : C.G₀ ≫ C.y' = C.U₁.ι ≫ pullback.fst _ _ ≫ y1 C.y C.R' := by
  rw [G₀, Category.assoc, C.ι.2, m₁_y1]

theorem henselian_R' : HenselianLocalRing C.R' :=
  HenselianLocalRing.of_moduleFinite_of_isLocalRing (R := C.R)

scoped instance isReduced_P : IsReduced C.P :=
  AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
    (pullback.fst (y1 C.y C.R') (y1 C.y C.R') ≫ y1 C.y C.R')

theorem dense_U₁ : Dense (C.U₁ : Set C.P) :=
  dense_of_forall_dense_fibre (fun q => (pullback.fst (y1 C.y C.R') (y1 C.y C.R')).base q) _ fun
    x₁ =>
    dense_fibre_of_isPullback (pullback.fst C.y C.y) (pullback.fst _ _) (pi1 C.y C.R') (p1 C.y
      C.R')
      (isPullback_pi1_fst C.y C.R') x₁ _ (C.hU₁ _)

theorem mem_U₁_of_ne (q : C.P) (hq : (pullback.fst (y1 C.y C.R') (y1 C.y C.R') ≫ y1 C.y C.R') q ≠
    IsLocalRing.closedPoint C.R') : q ∈ C.U₁ := by
  change pi1 C.y C.R' q ∈ C.U
  refine C.hUK _ fun h => hq ?_
  rw [← Scheme.Hom.comp_apply, pi1_fst_assoc, pullback.condition] at h
  set s : Spec (CommRingCat.of C.R') := (pullback.fst (y1 C.y C.R') (y1 C.y C.R') ≫ y1 C.y C.R')
    q with hs
  have h' : (bS C.R C.R') s = IsLocalRing.closedPoint C.R := by
    rw [hs, ← Scheme.Hom.comp_apply]; simpa only [Category.assoc] using h
  have hinj : Function.Injective (algebraMap C.R C.R') := FaithfulSMul.algebraMap_injective C.R
    C.R'
  have hcomap : s.asIdeal.comap (algebraMap C.R C.R') = IsLocalRing.maximalIdeal C.R := by
    exact congrArg PrimeSpectrum.asIdeal h'
  have hne : s.asIdeal ≠ ⊥ := by
    intro hbot
    rw [hbot, Ideal.comap_bot_of_injective _ hinj] at hcomap
    exact (IsDiscreteValuationRing.not_isField C.R)
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hcomap.symm)
  have hmax : s.asIdeal.IsMaximal := s.isPrime.isMaximal hne
  exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)

theorem exists_datum (t : C.P)
    (ht : (pullback.fst (y1 C.y C.R') (y1 C.y C.R') ≫ y1 C.y C.R') t = IsLocalRing.closedPoint
      C.R') :
    ∃ (R'' : Type u) (_ : CommRing R'') (_ : IsDomain R'') (_ : IsDiscreteValuationRing R'') (_
      : Algebra C.R' R'')
      (_ : Module.Finite C.R' R'') (_ : Algebra.Etale C.R' R'') (_ : Module.FaithfullyFlat C.R'
        R'')
      (a : Spec (CommRingCat.of R'') ⟶ C.Y) (T : Scheme.{u}) (t'' : T ⟶ Spec (CommRingCat.of R''))
      (w₁ w₂ : T ⟶ (C.U : Scheme.{u})) (s : T ⟶ C.P),
      a ≫ C.y = bS C.R' R'' ≫ bS C.R C.R' ∧
      w₁ ≫ C.U.ι ≫ pullback.fst C.y C.y = t'' ≫ a ∧
      w₂ ≫ C.U.ι ≫ pullback.fst C.y C.y = w₁ ≫ C.U.ι ≫ pullback.snd C.y C.y ∧
      s ≫ pullback.fst _ _ ≫ p1 C.y C.R' = w₁ ≫ C.m.1 ∧
      s ≫ pullback.snd _ _ ≫ p1 C.y C.R' = w₂ ≫ C.U.ι ≫ pullback.snd C.y C.y ∧
      s ≫ pullback.fst _ _ ≫ y1 C.y C.R' = t'' ≫ bS C.R' R'' ∧
      t ∈ Set.range s.base := by
  let fst' := pullback.fst (y1 C.y C.R') (y1 C.y C.R'); let snd' := pullback.snd (y1 C.y C.R') (y1
    C.y C.R')
  let K : Type u := C.P.residueField t
  let pt : Spec (CommRingCat.of K) ⟶ C.P := C.P.fromSpecResidueField t
  let x₁ : Spec (CommRingCat.of K) ⟶ Y1 C.y C.R' := pt ≫ fst'
  let v₁ : Spec (CommRingCat.of K) ⟶ Y1 C.y C.R' := pt ≫ snd'
  let xK : Spec (CommRingCat.of K) ⟶ C.Y := x₁ ≫ p1 C.y C.R'
  let vK : Spec (CommRingCat.of K) ⟶ C.Y := v₁ ≫ p1 C.y C.R'
  let c₁ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of C.R') := x₁ ≫ y1 C.y C.R'
  let cK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of C.R) := c₁ ≫ bS C.R C.R'
  have hxK : xK ≫ C.y = cK := by simp only [xK, cK, c₁, Category.assoc, pullback.condition]
  have hv₁c : v₁ ≫ y1 C.y C.R' = c₁ := by simp only [v₁, c₁, x₁, Category.assoc]; rw
    [pullback.condition]
  have hvK : vK ≫ C.y = cK := by
    simp only [vK, cK, Category.assoc, pullback.condition]; rw [reassoc_of% hv₁c]
  have hxK' : xK = Spec.map ((fst' ≫ p1 C.y C.R').residueFieldMap t) ≫ C.Y.fromSpecResidueField
    ((fst' ≫ p1 C.y C.R') t) := by
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]; simp only [xK, x₁, pt,
      Category.assoc]
  have hvK' : vK = Spec.map ((snd' ≫ p1 C.y C.R').residueFieldMap t) ≫ C.Y.fromSpecResidueField
    ((snd' ≫ p1 C.y C.R') t) := by
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]; simp only [vK, v₁, pt,
      Category.assoc]
  let lam := lamSnd C.y cK xK hxK
  let lam' := lamFst C.y cK xK hxK
  let lamv := lamSnd C.y cK vK hvK
  let e₁ := pullback.fst lam (Phi C.y C.U C.m)
  have : IsOpenImmersion e₁ :=
    MorphismProperty.of_isPullback
      (P := (@IsOpenImmersion : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback lam (Phi C.y C.U C.m)).flip C.hΦ
  let β := pullback.snd lam (Phi C.y C.U C.m)
  have hd₁ : Dense (Set.range e₁) := by
    rw [Scheme.Pullback.range_fst]
    exact dense_preimage_of_isPullback (pullback.snd C.y C.y) _ (Spec.map ((fst' ≫ p1 C.y
      C.R').residueFieldMap t))
      xK hxK' (isPullback_lamSnd C.y cK xK hxK) _ (C.hΦ₂ _)
  have hPhi₁ : Phi C.y C.U C.m ≫ pullback.fst C.y C.y = C.U.ι ≫ pullback.fst C.y C.y :=
    pullback.lift_fst _ _ _
  have hPhi₂ : Phi C.y C.U C.m ≫ pullback.snd C.y C.y = C.m.1 := pullback.lift_snd _ _ _
  have hν₀ : (β ≫ C.U.ι ≫ pullback.snd C.y C.y) ≫ C.y = (e₁ ≫ pullback.snd C.y cK) ≫ cK := by
    calc (β ≫ C.U.ι ≫ pullback.snd C.y C.y) ≫ C.y = β ≫ (Phi C.y C.U C.m ≫ pullback.fst C.y C.y)
      ≫ C.y := by
          rw [hPhi₁]; simp only [Category.assoc, pullback.condition]
      _ = (e₁ ≫ lam) ≫ pullback.fst C.y C.y ≫ C.y := by
          simp only [Category.assoc]; rw [pullback.condition_assoc]
      _ = (e₁ ≫ pullback.snd C.y cK) ≫ cK := by
          simp only [Category.assoc, lam, lamSnd_fst_assoc]
          rw [pullback.condition]
  let ν : pullback lam (Phi C.y C.U C.m) ⟶ pullback C.y cK :=
    pullback.lift (β ≫ C.U.ι ≫ pullback.snd C.y C.y) (e₁ ≫ pullback.snd C.y cK) hν₀
  have hν₁ : ν ≫ pullback.fst C.y cK = β ≫ C.U.ι ≫ pullback.snd C.y C.y := pullback.lift_fst _ _ _
  have hν₂ : ν ≫ pullback.snd C.y cK = e₁ ≫ pullback.snd C.y cK := pullback.lift_snd _ _ _
  have hνsq : IsPullback ν β lam' (Psi C.y C.U C.m) := by
    refine IsPullback.of_right (h₁₂ := pullback.snd C.y cK) (v₁₃ := xK) (h₂₂ := pullback.fst C.y
      C.y) ?_ ?_
      (isPullback_lamFst C.y cK xK hxK)
    · rw [hν₂, pullback.lift_fst]
      have h := (IsPullback.of_hasPullback lam (Phi C.y C.U C.m)).paste_horiz (isPullback_lamSnd
        C.y cK xK hxK)
      rwa [hPhi₂] at h
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst]
        change ν ≫ lamFst C.y cK xK hxK ≫ pullback.fst C.y C.y = β ≫ C.m.1
        rw [lamFst_fst, reassoc_of% hν₂, ← hPhi₂, ← pullback.condition_assoc]
        change e₁ ≫ pullback.snd C.y cK ≫ xK = e₁ ≫ lamSnd C.y cK xK hxK ≫ pullback.snd C.y C.y
        rw [lamSnd_snd]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd]
        change ν ≫ lamFst C.y cK xK hxK ≫ pullback.snd C.y C.y = β ≫ C.U.ι ≫ pullback.snd C.y C.y
        rw [lamFst_snd, hν₁]
  have : IsOpenImmersion ν := MorphismProperty.of_isPullback (P := (@IsOpenImmersion :
    MorphismProperty Scheme.{u})) hνsq.flip C.hΨ
  have hd₂ : Dense ((ν ≫ lamv) ⁻¹' (C.U : Set ↑(pullback C.y C.y))) := by
    have h := dense_preimage_of_isPullback (pullback.snd C.y C.y) _
      (Spec.map ((snd' ≫ p1 C.y C.R').residueFieldMap t)) vK hvK' (isPullback_lamSnd C.y cK vK
        hvK) _ (C.hU₂ _)
    exact h.preimage ν.isOpenMap
  let Zt : (pullback C.y cK).Opens := e₁ ''ᵁ ((ν ≫ lamv) ⁻¹ᵁ C.U)
  have hZt : Dense (Zt : Set ↑(pullback C.y cK)) := DenseRange.dense_image hd₁ e₁.continuous hd₂
  let κ₁ : pullback C.y cK ⟶ Y1 C.y C.R' :=
    pullback.lift (pullback.fst C.y cK) (pullback.snd C.y cK ≫ c₁) (by rw [pullback.condition,
      Category.assoc])
  have hκ₁p : κ₁ ≫ p1 C.y C.R' = pullback.fst C.y cK := pullback.lift_fst _ _ _
  have hκ₁y : κ₁ ≫ y1 C.y C.R' = pullback.snd C.y cK ≫ c₁ := pullback.lift_snd _ _ _
  have hκ₁ : IsPullback κ₁ (pullback.snd C.y cK) (y1 C.y C.R') c₁ := by
    refine IsPullback.of_right (h₁₂ := p1 C.y C.R') (v₁₃ := C.y) (h₂₂ := bS C.R C.R') ?_ hκ₁y
      (IsPullback.of_hasPullback C.y (bS C.R C.R'))
    rw [hκ₁p]
    exact IsPullback.of_hasPullback C.y cK
  let s₀ : Spec (CommRingCat.of C.R') := (fst' ≫ y1 C.y C.R') t
  let k : Spec (CommRingCat.of K) ⟶ Spec ((Spec (CommRingCat.of C.R')).residueField s₀) :=
    Spec.map ((fst' ≫ y1 C.y C.R').residueFieldMap t)
  have hc₁ : c₁ = k ≫ (Spec (CommRingCat.of C.R')).fromSpecResidueField s₀ := by
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]; simp only [c₁, x₁, pt,
      Category.assoc]
  let fib := (y1 C.y C.R').fiber s₀
  let e : pullback C.y cK ⟶ fib :=
    pullback.lift κ₁ (pullback.snd C.y cK ≫ k) (by rw [hκ₁y, Category.assoc, ← hc₁])
  have heι : e ≫ (y1 C.y C.R').fiberι s₀ = κ₁ := pullback.lift_fst _ _ _
  have he : IsPullback e (pullback.snd C.y cK) ((y1 C.y C.R').fiberToSpecResidueField s₀) k := by
    refine IsPullback.of_right (h₁₂ := (y1 C.y C.R').fiberι s₀) (v₁₃ := y1 C.y C.R')
      (h₂₂ := (Spec (CommRingCat.of C.R')).fromSpecResidueField s₀) ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback _ _)
    rw [heι, ← hc₁]
    exact hκ₁
  have : UniversallyOpen e := MorphismProperty.of_isPullback (P := @UniversallyOpen) he.flip
    inferInstance
  have hV₀ : IsOpen (e.base '' (Zt : Set ↑(pullback C.y cK))) := e.isOpenMap _ Zt.2
  obtain ⟨O, hOo, hOpre⟩ :=
    ((y1 C.y C.R').fiberι s₀).isEmbedding.isInducing.isOpen_iff.mp hV₀
  let OO : (Y1 C.y C.R').Opens := ⟨O, hOo⟩
  have : Nonempty ↑(pullback C.y cK) := ⟨(pullback.lift xK (𝟙 _) (by rw [hxK, Category.id_comp]) :
    Spec (CommRingCat.of K) ⟶ pullback C.y cK) (IsLocalRing.closedPoint K)⟩
  obtain ⟨z₀, hz₀⟩ := hZt.nonempty
  let x : Y1 C.y C.R' := (y1 C.y C.R').fiberι s₀ (e z₀)
  have hx : (y1 C.y C.R') x = IsLocalRing.closedPoint C.R' := by
    have : x ∈ (y1 C.y C.R') ⁻¹' {s₀} := by
      rw [← Scheme.Hom.range_fiberι]; exact ⟨_, rfl⟩
    rw [this]; exact ht
  have hxV : x ∈ OO := by
    change (y1 C.y C.R').fiberι s₀ (e z₀) ∈ O
    rw [← Set.mem_preimage, hOpre]
    exact ⟨z₀, hz₀, rfl⟩
  have : HenselianLocalRing C.R' := C.henselian_R'
  obtain ⟨R'', _, _, _, _, _, _, _, hloc, _, a₁, -, ha₁, hmem⟩ :=
    (open AlgebraicGeometry.Smooth in
      exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing
      (y1 C.y C.R') OO x hx hxV)
  let a₀ : Y1 C.y C.R' := a₁ (IsLocalRing.closedPoint R'')
  have ha₀ : (y1 C.y C.R') a₀ = s₀ := by
    let ptR : Spec (CommRingCat.of R'') := IsLocalRing.closedPoint R''
    change (a₁ ≫ y1 C.y C.R') ptR = s₀
    rw [ha₁]
    have : IsLocalHom (CommRingCat.ofHom (algebraMap C.R' R'')).hom := by rwa
      [CommRingCat.hom_ofHom]
    rw [Spec_closedPoint]
    exact ht.symm
  obtain ⟨f₀, hf₀⟩ : a₀ ∈ Set.range ((y1 C.y C.R').fiberι s₀) := by
    rw [Scheme.Hom.range_fiberι]; exact ha₀
  have hf₀O : f₀ ∈ (y1 C.y C.R').fiberι s₀ ⁻¹' O := by
    rw [Set.mem_preimage, hf₀]; exact hmem
  rw [hOpre] at hf₀O
  obtain ⟨z, hz, hez⟩ := hf₀O
  have hκz : κ₁ z = a₁ (IsLocalRing.closedPoint R'') := by
    rw [← heι, Scheme.Hom.comp_apply, hez, hf₀]
  obtain ⟨μ, hμ₁, hμ₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := κ₁) (g := a₁) z
    (IsLocalRing.closedPoint R'') hκz
  let M := pullback κ₁ a₁
  let L : Type u := M.residueField μ
  let l₀ : Spec (CommRingCat.of L) ⟶ M := M.fromSpecResidueField μ
  let zL : Spec (CommRingCat.of L) ⟶ pullback C.y cK := l₀ ≫ pullback.fst κ₁ a₁
  let lR : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R'') := l₀ ≫ pullback.snd κ₁ a₁
  let lL : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) := zL ≫ pullback.snd C.y cK
  have hzL : Set.range zL.base ⊆ (Zt : Set ↑(pullback C.y cK)) := by
    rintro _ ⟨p, rfl⟩
    change (l₀ ≫ pullback.fst κ₁ a₁) p ∈ Zt
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply, hμ₁]
    exact hz
  have hr : Set.range zL.base ⊆ Set.range e₁.base := hzL.trans (Set.image_subset_range _ _)
  let a₁' := IsOpenImmersion.lift e₁ zL hr
  have ha₁' : a₁' ≫ e₁ = zL := IsOpenImmersion.lift_fac _ _ _
  have hμC.U : ∀ p, (a₁' ≫ ν ≫ lamv) p ∈ C.U := by
    intro p
    obtain ⟨z', hz', hze⟩ := hzL ⟨p, rfl⟩
    rw [← ha₁', Scheme.Hom.comp_apply] at hze
    rw [Scheme.Hom.comp_apply, ← e₁.isOpenEmbedding.injective hze]
    exact hz'
  let μK := a₁' ≫ ν ≫ lamv
  let w₂ : Spec (CommRingCat.of L) ⟶ C.U := IsOpenImmersion.lift C.U.ι μK (by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨p, rfl⟩; exact hμC.U p)
  have hw₂ : w₂ ≫ C.U.ι = μK := IsOpenImmersion.lift_fac _ _ _
  let w₁ : Spec (CommRingCat.of L) ⟶ C.U := a₁' ≫ β
  let a : Spec (CommRingCat.of R'') ⟶ C.Y := a₁ ≫ p1 C.y C.R'
  let s : Spec (CommRingCat.of L) ⟶ C.P := lL ≫ pt
  have hβΦ : β ≫ Phi C.y C.U C.m = e₁ ≫ lam := pullback.condition.symm
  have hMcond : pullback.fst κ₁ a₁ ≫ κ₁ = pullback.snd κ₁ a₁ ≫ a₁ := pullback.condition
  refine ⟨R'', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance,
    a, Spec (CommRingCat.of L), lR, w₁, w₂, s, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [a, Category.assoc]; rw [pullback.condition, reassoc_of% ha₁]
  · calc w₁ ≫ C.U.ι ≫ pullback.fst C.y C.y = a₁' ≫ β ≫ Phi C.y C.U C.m ≫ pullback.fst C.y C.y := by
          simp only [w₁, Category.assoc, hPhi₁]
      _ = zL ≫ pullback.fst C.y cK := by rw [reassoc_of% hβΦ, reassoc_of% ha₁']; simp only [lam,
        lamSnd_fst]
      _ = lR ≫ a := by
          simp only [zL, lR, a, Category.assoc, ← hκ₁p]
          rw [reassoc_of% hMcond]
  · rw [reassoc_of% hw₂]
    simp only [μK, w₁, Category.assoc, lamv, lamSnd_fst, hν₁]
  · calc s ≫ fst' ≫ p1 C.y C.R' = lL ≫ xK := by simp only [s, lL, xK, x₁, Category.assoc]
      _ = zL ≫ lam ≫ pullback.snd C.y C.y := by simp only [lL, lam, lamSnd_snd, Category.assoc]
      _ = w₁ ≫ C.m.1 := by rw [← reassoc_of% ha₁', ← reassoc_of% hβΦ, hPhi₂]; simp only [w₁,
        Category.assoc]
  · calc s ≫ snd' ≫ p1 C.y C.R' = lL ≫ vK := by simp only [s, lL, vK, v₁, Category.assoc]
      _ = w₂ ≫ C.U.ι ≫ pullback.snd C.y C.y := by
          rw [reassoc_of% hw₂]
          simp only [μK, lL, Category.assoc, lamv, lamSnd_snd, reassoc_of% hν₂, reassoc_of% ha₁']
  · calc s ≫ fst' ≫ y1 C.y C.R' = zL ≫ pullback.snd C.y cK ≫ c₁ := by simp only [s, lL, c₁, x₁,
      Category.assoc]
      _ = zL ≫ κ₁ ≫ y1 C.y C.R' := by rw [hκ₁y]
      _ = lR ≫ bS C.R' R'' := by
          simp only [zL, lR, Category.assoc]
          rw [reassoc_of% hMcond, ha₁]
  · let q : Spec (CommRingCat.of L) := IsLocalRing.closedPoint L
    refine ⟨q, ?_⟩
    change (lL ≫ pt) q = t
    exact (Scheme.Hom.comp_apply lL pt q).trans
      (Scheme.fromSpecResidueField_apply _ _)

/-- Agreement with multiplication on the common dense domain. -/
def Agree (V : C.P.Opens) (G : (V : Scheme.{u}) ⟶ C.Y') : Prop :=
  ∀ {T : Scheme.{u}} (s : T ⟶ (V : Scheme.{u})) (w : T ⟶ (C.U : Scheme.{u})) (v : T ⟶ Y1 C.y C.R'),
    s ≫ V.ι ≫ pullback.fst _ _ ≫ p1 C.y C.R' = w ≫ C.U.ι ≫ pullback.fst C.y C.y →
    s ≫ V.ι ≫ pullback.snd _ _ ≫ p1 C.y C.R' = w ≫ C.U.ι ≫ pullback.snd C.y C.y →
    v ≫ p1 C.y C.R' = w ≫ C.m.1 →
    v ≫ y1 C.y C.R' = s ≫ V.ι ≫ pullback.fst _ _ ≫ y1 C.y C.R' →
    s ≫ G = v ≫ C.ι.1

theorem G₀_agree : C.Agree C.U₁ C.G₀ := by
  intro T s w v h₁ h₂ h₃ h₄
  rw [G₀, ← Category.assoc]
  congr 1
  have hsw : s ≫ C.πU = w := by
    rw [← cancel_mono C.U.ι]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, πU_fst]; exact h₁
    · rw [Category.assoc, Category.assoc, πU_snd]; exact h₂
  apply pullback.hom_ext
  · rw [Category.assoc, m₁_p1, reassoc_of% hsw, h₃]
  · rw [Category.assoc, m₁_y1, h₄]

theorem hpiece (t : C.P) : ∃ (V : C.P.Opens) (G : (V : Scheme.{u}) ⟶ C.Y'),
    G ≫ C.y' = V.ι ≫ pullback.fst _ _ ≫ y1 C.y C.R' ∧ C.Agree V G ∧ t ∈ V := by
  by_cases ht : (pullback.fst (y1 C.y C.R') (y1 C.y C.R') ≫ y1 C.y C.R') t =
    IsLocalRing.closedPoint C.R'
  · obtain ⟨R'', _, _, _, _, _, _, _, a, T, t'', w₁, w₂, s, ha, hw₁, hw₂, hs₁, hs₂, hs₃, hts⟩ :=
    C.exists_datum t ht
    obtain ⟨τ, hτ₁, hτ₂⟩ := C.hstat R'' inferInstance inferInstance inferInstance inferInstance
      inferInstance
      inferInstance inferInstance a ha
    obtain ⟨V, G, hagree, hmemV⟩ :=
      NeronModelInfra.exists_opens_forall_range_subset_of_comp_translation_eq_of_etale
        C.y C.U C.m C.hU₁ C.hΦ C.hassoc C.R' C.y' C.ι R'' a ha τ hτ₁ hτ₂
    refine ⟨V, G.1, G.2, fun s w v => hagree s w v, ?_⟩
    obtain ⟨p, rfl⟩ := hts
    exact hmemV t'' w₁ w₂ s hw₁ hw₂ hs₁ hs₂ hs₃ ⟨p, rfl⟩
  · exact ⟨C.U₁, C.G₀, C.G₀_y', C.G₀_agree, C.mem_U₁_of_ne t ht⟩

/-- The open pieces used to glue the extended multiplication. -/
def PF (V : C.P → C.P.Opens) : Option C.P → Scheme.{u}
  | none => (C.U₁ : Scheme.{u})
  | some t => (V t : Scheme.{u})

/-- The inclusions of the gluing pieces. -/
def Pj (V : C.P → C.P.Opens) : ∀ o, C.PF V o ⟶ C.P
  | none => C.U₁.ι
  | some t => (V t).ι

/-- The local maps on the gluing pieces. -/
def Pg (V : C.P → C.P.Opens) (G : ∀ t, (V t : Scheme.{u}) ⟶ C.Y') : ∀ o, C.PF V o ⟶ C.Y'
  | none => C.G₀
  | some t => G t

scoped instance isOpenImmersion_Pj (V : C.P → C.P.Opens) (o : Option C.P) : IsOpenImmersion
  (C.Pj V o) := by
  cases o with
  | none => exact inferInstanceAs (IsOpenImmersion C.U₁.ι)
  | some t => exact inferInstanceAs (IsOpenImmersion (V t).ι)

theorem exists_G : ∃ G : C.P ⟶ C.Y', C.U₁.ι ≫ G = C.G₀ ∧ G ≫ C.y' = pullback.fst _ _ ≫ y1 C.y
  C.R' := by
  choose V G hGy hGa hmem using C.hpiece
  have hPy : ∀ o, C.Pg V G o ≫ C.y' = C.Pj V o ≫ pullback.fst _ _ ≫ y1 C.y C.R' := by
    rintro (_ | t)
    · exact C.G₀_y'
    · exact hGy t
  have hAg : ∀ o {T : Scheme.{u}} (s : T ⟶ C.PF V o) (w : T ⟶ (C.U : Scheme.{u})) (v : T ⟶ Y1
    C.y C.R'),
      s ≫ C.Pj V o ≫ pullback.fst _ _ ≫ p1 C.y C.R' = w ≫ C.U.ι ≫ pullback.fst C.y C.y →
      s ≫ C.Pj V o ≫ pullback.snd _ _ ≫ p1 C.y C.R' = w ≫ C.U.ι ≫ pullback.snd C.y C.y →
      v ≫ p1 C.y C.R' = w ≫ C.m.1 →
      v ≫ y1 C.y C.R' = s ≫ C.Pj V o ≫ pullback.fst _ _ ≫ y1 C.y C.R' →
      s ≫ C.Pg V G o = v ≫ C.ι.1 := by
    rintro (_ | t)
    · exact fun s w v => C.G₀_agree s w v
    · exact fun s w v => hGa t s w v
  obtain ⟨GG, hGG, hGGy⟩ := exists_glue_of_isOpenImmersion (pullback.fst _ _ ≫ y1 C.y C.R') C.y'
    (C.PF V) (C.Pj V)
    (fun t => ⟨some t, ⟨t, hmem t⟩, Scheme.Opens.ι_apply _ _⟩) (C.Pg V G) hPy
    (fun o o' => by
      refine ⟨(C.U₁ : Set C.P), C.U₁.2, ?_, ?_⟩
      · rw [C.dense_U₁.closure_eq]; exact Set.subset_univ _
      · intro T t₁ t₂ h hW
        have hr : Set.range (t₁ ≫ C.Pj V o ≫ pi1 C.y C.R').base ⊆ Set.range C.U.ι.base := by
          rw [Scheme.Opens.range_ι]
          rintro _ ⟨p, rfl⟩
          rw [← Category.assoc, Scheme.Hom.comp_apply]
          exact hW ⟨p, rfl⟩
        let w := IsOpenImmersion.lift C.U.ι _ hr
        have hw : w ≫ C.U.ι = t₁ ≫ C.Pj V o ≫ pi1 C.y C.R' := IsOpenImmersion.lift_fac _ _ _
        have hv : (w ≫ C.m.1) ≫ C.y = (t₁ ≫ C.Pj V o ≫ pullback.fst _ _ ≫ y1 C.y C.R') ≫ bS C.R
          C.R' := by
          rw [Category.assoc, C.m.2, reassoc_of% hw]
          simp only [Category.assoc, pi1_fst_assoc]
          rw [pullback.condition]
        let v : T ⟶ Y1 C.y C.R' := pullback.lift _ _ hv
        have e₁ := hAg o t₁ w v (by rw [reassoc_of% hw, pi1_fst]) (by rw [reassoc_of% hw, pi1_snd])
          (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
        have e₂ := hAg o' t₂ w v (by rw [reassoc_of% hw, pi1_fst, reassoc_of% h])
          (by rw [reassoc_of% hw, pi1_snd, reassoc_of% h]) (pullback.lift_fst _ _ _)
          (by rw [pullback.lift_snd, reassoc_of% h])
        rw [e₁, e₂])
  exact ⟨GG, hGG none, hGGy⟩

theorem exists_extension :
    ∃ (D : (pullback C.y' C.y').Opens) (hle : C.U' ≤ D)
      (M : SchemeHomOver (D.ι ≫ pullback.fst C.y' C.y' ≫ C.y') C.y'),
      (pullback C.y' C.y').homOfLE hle ≫ M.1 = C.m'.1 ∧
      ∀ q : ↑(pullback C.y' C.y'), (pullback.fst C.y' C.y').base q ∈ Set.range C.ι.1.base →
        (pullback.snd C.y' C.y').base q ∈ Set.range C.ι.1.base → q ∈ D := by
  obtain ⟨G, hGU, hGy⟩ := C.exists_G
  let ιι : C.P ⟶ pullback C.y' C.y' :=
    pullback.map _ _ _ _ C.ι.1 C.ι.1 (𝟙 _) (by rw [Category.comp_id, C.ι.2]) (by rw
      [Category.comp_id, C.ι.2])
  have hιι₁ : ιι ≫ pullback.fst C.y' C.y' = pullback.fst _ _ ≫ C.ι.1 := pullback.lift_fst _ _ _
  have hιι₂ : ιι ≫ pullback.snd C.y' C.y' = pullback.snd _ _ ≫ C.ι.1 := pullback.lift_snd _ _ _
  have : IsReduced (pullback C.y' C.y') :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (pullback.fst C.y'
      C.y' ≫ C.y')
  let D : (pullback C.y' C.y').Opens := C.U' ⊔ ιι.opensRange
  have hU'D : C.U' ≤ D := le_sup_left
  have : IsReduced (D : Scheme.{u}) := isReduced_of_isOpenImmersion D.ι
  let F : Bool → Scheme.{u} := fun b => bif b then (C.U' : Scheme.{u}) else C.P
  have hr₂ : Set.range ιι.base ⊆ Set.range D.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact fun q hq => Or.inr hq
  let j₂ : C.P ⟶ D := IsOpenImmersion.lift D.ι ιι hr₂
  have hj₂ : j₂ ≫ D.ι = ιι := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion j₂ := by
    have : IsOpenImmersion (j₂ ≫ D.ι) := by rw [hj₂]; infer_instance
    exact IsOpenImmersion.of_comp j₂ D.ι
  let j : ∀ b, F b ⟶ D := fun b =>
    match b with
    | true => (pullback C.y' C.y').homOfLE hU'D
    | false => j₂
  have : ∀ b, IsOpenImmersion (j b) := by
    rintro (_ | _)
    · exact inferInstanceAs (IsOpenImmersion j₂)
    · exact inferInstanceAs (IsOpenImmersion ((pullback C.y' C.y').homOfLE hU'D))
  let g : ∀ b, F b ⟶ C.Y' := fun b =>
    match b with
    | true => C.m'.1
    | false => G
  have hcovt : ∀ x : D, x.1 ∈ C.U' → x ∈ Set.range ((pullback C.y' C.y').homOfLE hU'D).base := by
    intro x hx
    refine ⟨⟨x.1, hx⟩, ?_⟩
    exact Scheme.homOfLE_apply' hU'D x.1 hx
  have hcovf : ∀ x : D, x.1 ∈ Set.range ιι.base → x ∈ Set.range j₂.base := by
    rintro x ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply D.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hj₂, Scheme.Opens.ι_apply, hq]
  have hcov : ∀ x : D, ∃ b, x ∈ Set.range (j b).base := by
    rintro ⟨x, hx | hx⟩
    · exact ⟨true, hcovt _ hx⟩
    · exact ⟨false, hcovf _ hx⟩
  let W : Set D := D.ι.base ⁻¹' (ιι.base '' (C.U₁ : Set C.P))
  have hWo : IsOpen W := (ιι.isOpenMap _ C.U₁.2).preimage D.ι.continuous
  have hWcl : Set.range j₂.base ⊆ closure W := by
    rintro _ ⟨q, rfl⟩
    have h1 : Set.range ιι.base ⊆ closure (ιι.base '' (C.U₁ : Set C.P)) := by
      rw [← Set.image_univ, ← C.dense_U₁.closure_eq]
      exact image_closure_subset_closure_image ιι.continuous
    have h2 : D.ι (j₂ q) ∈ closure (ιι.base '' (C.U₁ : Set C.P)) := by
      rw [← Scheme.Hom.comp_apply, hj₂]
      exact h1 ⟨q, rfl⟩
    change j₂ q ∈ closure (D.ι.base ⁻¹' _)
    rw [← D.ι.isOpenMap.preimage_closure_eq_closure_preimage D.ι.continuous]
    exact h2
  have hagree : ∀ {T : Scheme.{u}} (t₁ : T ⟶ C.U') (t₂ : T ⟶ C.P),
      t₁ ≫ (pullback C.y' C.y').homOfLE hU'D = t₂ ≫ j₂ →
      Set.range (t₁ ≫ (pullback C.y' C.y').homOfLE hU'D).base ⊆ W → t₁ ≫ C.m'.1 = t₂ ≫ G := by
    intro T t₁ t₂ h hW
    have hr : Set.range t₂.base ⊆ Set.range C.U₁.ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      have hp : D.ι ((t₁ ≫ (pullback C.y' C.y').homOfLE hU'D) p) ∈ ιι.base '' (C.U₁ : Set C.P) :=
        hW ⟨p, rfl⟩
      rw [h, ← Scheme.Hom.comp_apply, Category.assoc, hj₂, Scheme.Hom.comp_apply] at hp
      obtain ⟨z, hz, hzq⟩ := hp
      rwa [← ιι.isOpenEmbedding.injective hzq]
    let wU := IsOpenImmersion.lift C.U₁.ι t₂ hr
    have hwU : wU ≫ C.U₁.ι = t₂ := IsOpenImmersion.lift_fac _ _ _
    let t' : T ⟶ Spec (CommRingCat.of C.R') := wU ≫ C.U₁.ι ≫ pullback.fst _ _ ≫ y1 C.y C.R'
    have ht' : t' = wU ≫ C.U₁.ι ≫ pullback.snd _ _ ≫ y1 C.y C.R' := by
      simp only [t', pullback.condition]
    let w : SchemeHomOver (t' ≫ bS C.R C.R') (C.U.ι ≫ pullback.fst C.y C.y ≫ C.y) :=
      ⟨wU ≫ C.πU, by
        rw [Category.assoc, πU_fst_assoc, pullback.condition (f := C.y) (g := bS C.R C.R')]
        simp only [t', Category.assoc]⟩
    have ha : (w.1 ≫ C.U.ι ≫ pullback.fst C.y C.y) ≫ C.y = t' ≫ bS C.R C.R' := by
      simpa only [Category.assoc] using w.2
    have hb : (w.1 ≫ C.U.ι ≫ pullback.snd C.y C.y) ≫ C.y = t' ≫ bS C.R C.R' := by
      have e : (w.1 ≫ C.U.ι ≫ pullback.snd C.y C.y) ≫ C.y = (w.1 ≫ C.U.ι ≫ pullback.fst C.y C.y)
        ≫ C.y := by
        simp only [Category.assoc, pullback.condition]
      exact e.trans ha
    have hc : (w.1 ≫ C.m.1) ≫ C.y = t' ≫ bS C.R C.R' := by
      rw [Category.assoc, C.m.2]; exact ha
    obtain ⟨w', hw'₁, hw'₂, hw'₃⟩ := C.hext t' w ⟨_, ha⟩ ⟨_, hb⟩ ⟨_, hc⟩ rfl rfl rfl
    rw [RelativeGroupLaw.baseChangePointOfBase_coe] at hw'₁ hw'₂ hw'₃
    have e₁ : pullback.lift (w.1 ≫ C.U.ι ≫ pullback.fst C.y C.y) t' ha = wU ≫ C.U₁.ι ≫
      pullback.fst _ _ := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        change (wU ≫ C.πU) ≫ C.U.ι ≫ pullback.fst C.y C.y = (wU ≫ C.U₁.ι ≫ pullback.fst _ _) ≫ p1
          C.y C.R'
        simp only [Category.assoc, πU_fst]
      · rw [pullback.lift_snd]; simp only [Category.assoc, t']
    have e₂ : pullback.lift (w.1 ≫ C.U.ι ≫ pullback.snd C.y C.y) t' hb = wU ≫ C.U₁.ι ≫
      pullback.snd _ _ := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        change (wU ≫ C.πU) ≫ C.U.ι ≫ pullback.snd C.y C.y = (wU ≫ C.U₁.ι ≫ pullback.snd _ _) ≫ p1
          C.y C.R'
        simp only [Category.assoc, πU_snd]
      · rw [pullback.lift_snd, ht']; simp only [Category.assoc]
    have e₃ : pullback.lift (w.1 ≫ C.m.1) t' hc = wU ≫ C.m₁ := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        change (wU ≫ C.πU) ≫ C.m.1 = (wU ≫ C.m₁) ≫ p1 C.y C.R'
        simp only [Category.assoc, m₁_p1]
      · rw [pullback.lift_snd, Category.assoc, m₁_y1]
    have ht₁ : t₁ = w'.1 := by
      rw [← cancel_mono C.U'.ι]
      have h' : t₁ ≫ C.U'.ι = t₂ ≫ ιι := by
        rw [← hj₂, ← Category.assoc, ← h, Category.assoc, Scheme.homOfLE_ι]
      rw [h', ← hwU]
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hιι₁, Category.assoc, hw'₁, e₁, Category.assoc,
        Category.assoc]
      · rw [Category.assoc, Category.assoc, hιι₂, Category.assoc, hw'₂, e₂, Category.assoc,
        Category.assoc]
    rw [ht₁, hw'₃, e₃, ← hwU, Category.assoc, Category.assoc, hGU, G₀]
  have hdiag : ∀ b, ∃ W : Set D, IsOpen W ∧ Set.range (j b).base ∩ Set.range (j b).base ⊆
    closure W ∧
      ∀ {T : Scheme.{u}} (t₁ t₂ : T ⟶ F b), t₁ ≫ j b = t₂ ≫ j b → Set.range (t₁ ≫ j b).base ⊆ W →
        t₁ ≫ g b = t₂ ≫ g b := by
    intro b
    refine ⟨Set.univ, isOpen_univ, by rw [closure_univ]; exact Set.subset_univ _, ?_⟩
    intro T t₁ t₂ h _
    rw [(cancel_mono (j b)).mp h]
  obtain ⟨M, hM, hMy⟩ := exists_glue_of_isOpenImmersion (D.ι ≫ pullback.fst C.y' C.y' ≫ C.y')
    C.y' F j hcov g
    (by
      rintro (_ | _)
      · change G ≫ C.y' = j₂ ≫ D.ι ≫ pullback.fst C.y' C.y' ≫ C.y'
        rw [hGy, ← Category.assoc j₂, hj₂, ← Category.assoc, hιι₁, Category.assoc, C.ι.2]
      · change C.m'.1 ≫ C.y' = (pullback C.y' C.y').homOfLE hU'D ≫ D.ι ≫ pullback.fst C.y' C.y'
        ≫ C.y'
        rw [C.m'.2, Scheme.homOfLE_ι_assoc])
    (by
      rintro (_ | _) (_ | _)
      · exact hdiag false
      · refine ⟨W, hWo, Set.inter_subset_left.trans hWcl, fun t₁ t₂ h hW => ?_⟩
        have hW' : Set.range (t₂ ≫ j true).base ⊆ W := by rwa [h] at hW
        exact (hagree t₂ t₁ h.symm hW').symm
      · exact ⟨W, hWo, Set.inter_subset_right.trans hWcl, fun t₁ t₂ h hW => hagree t₁ t₂ h hW⟩
      · exact hdiag true)
  refine ⟨D, hU'D, ⟨M, hMy⟩, hM true, ?_⟩
  rintro q ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
  refine Or.inr ?_
  change q ∈ Set.range ιι.base
  rw [Scheme.Pullback.range_map]
  exact ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩

end Cx

end TranslationDomains

end

end AbelianVarieties.NOSProofs.EtaleTranslationDomains

namespace NeronModelInfra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian Topology
open AbelianVarieties.NOSProofs.EtaleTranslationDomains

universe u

theorem exists_opens_forall_mem_of_mem_range_of_forall_exists_translation_of_henselianLocalRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback
        y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hU₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback
        y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (_hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback
        y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΦ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback
        y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (_hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback
        y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (_hΨ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback
        y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫
        pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y
        = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    (hUK : ∀ q : ↑(pullback y y), (pullback.fst y y ≫ y).base q ≠ IsLocalRing.closedPoint R → q
      ∈ U)
    (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [Module.Finite R R'] [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R'))
    [Smooth y'] [IsSeparated y'] [LocallyOfFiniteType y'] [QuasiCompact y']
    (ι : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y')
      [IsOpenImmersion ι.1]
    (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y')
    (hU'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y'))))
    (hU'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y'))))
    (hΦ' : IsOpenImmersion
      (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)))
    (hΦ'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base)))
    (hΦ'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base)))
    (hΨ' : IsOpenImmersion
      (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hΨ'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hassoc' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
        (u v p q : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y')),
      u.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.fst y' y' →
      p.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 → p.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫
        U'.ι ≫ pullback.snd y' y' →
      q.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U'.ι ≫ pullback.fst y' y' → q.1 ≫ U'.ι ≫
        pullback.snd y' y' = v.1 ≫ m'.1 →
      p.1 ≫ m'.1 = q.1 ≫ m'.1)
    (hext : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫
          pullback.fst y y ≫ y))
        (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y),
      a.1 = w.1 ≫ U.ι ≫ pullback.fst y y → b.1 = w.1 ≫ U.ι ≫ pullback.snd y y → c.1 = w.1 ≫ m.1 →
      ∃ w' : SchemeHomOver t' (U'.ι ≫ pullback.fst y' y' ≫ y'),
        w'.1 ≫ U'.ι ≫ pullback.fst y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map
          (CommRingCat.ofHom (algebraMap R R'))) a).1 ≫ ι.1 ∧
        w'.1 ≫ U'.ι ≫ pullback.snd y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map
          (CommRingCat.ofHom (algebraMap R R'))) b).1 ≫ ι.1 ∧
        w'.1 ≫ m'.1 = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom
          (algebraMap R R'))) c).1 ≫ ι.1)
    (hstat : ∀ (R'' : Type u) (_ : CommRing R'') (_ : IsDomain R'') (_ : IsDiscreteValuationRing
      R'')
        (_ : Algebra R' R'') (_ : Module.Finite R' R'') (_ : Algebra.Etale R' R'') (_ :
          Module.FaithfullyFlat R' R'')
        (a : Spec (CommRingCat.of R'') ⟶ Y),
      a ≫ y = (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom
        (algebraMap R R'))) →
      ∃ τ : pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map
        (CommRingCat.ofHom (algebraMap R R')))) ⟶ pullback y' (Spec.map (CommRingCat.ofHom
          (algebraMap R' R''))),
        τ ≫ pullback.snd y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = pullback.snd y
          ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom
            (algebraMap R R')))) ∧
        ∀ {T : Scheme.{u}} (x : T ⟶ pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R'
          R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))))
          (w : T ⟶ (U : Scheme.{u})) (v : T ⟶ pullback y (Spec.map (CommRingCat.ofHom
            (algebraMap R R')))),
          w ≫ U.ι ≫ pullback.fst y y = x ≫ pullback.snd y ((Spec.map (CommRingCat.ofHom
            (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ a →
          w ≫ U.ι ≫ pullback.snd y y = x ≫ pullback.fst y ((Spec.map (CommRingCat.ofHom
            (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) →
          v ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ m.1 →
          v ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = x ≫ pullback.snd
            y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom
              (algebraMap R R')))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) →
          x ≫ τ ≫ pullback.fst y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = v ≫ ι.1) :
    ∃ (U'' : (pullback y' y').Opens) (hle : U' ≤ U'')
      (m'' : SchemeHomOver (U''.ι ≫ pullback.fst y' y' ≫ y') y'),
      (pullback y' y').homOfLE hle ≫ m''.1 = m'.1 ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (U'' : Set ↑(pullback y' y')))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (U'' : Set ↑(pullback y' y')))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') (U''.ι ≫ pullback.fst y' y') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U''.ι ≫ pullback.fst y' y') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U''.ι ≫ pullback.fst y' y') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') m''.1 (U''.ι ≫ pullback.snd y' y')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m''.1 (U''.ι ≫ pullback.snd y' y')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m''.1 (U''.ι ≫ pullback.snd y' y')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
          (u v p q : SchemeHomOver t (U''.ι ≫ pullback.fst y' y' ≫ y')),
        u.1 ≫ U''.ι ≫ pullback.snd y' y' = v.1 ≫ U''.ι ≫ pullback.fst y' y' →
        p.1 ≫ U''.ι ≫ pullback.fst y' y' = u.1 ≫ m''.1 →
        p.1 ≫ U''.ι ≫ pullback.snd y' y' = v.1 ≫ U''.ι ≫ pullback.snd y' y' →
        q.1 ≫ U''.ι ≫ pullback.fst y' y' = u.1 ≫ U''.ι ≫ pullback.fst y' y' →
        q.1 ≫ U''.ι ≫ pullback.snd y' y' = v.1 ≫ m''.1 →
        p.1 ≫ m''.1 = q.1 ≫ m''.1) ∧
      (∀ q : ↑(pullback y' y'), (pullback.fst y' y').base q ∈ Set.range ι.1.base →
        (pullback.snd y' y').base q ∈ Set.range ι.1.base → q ∈ U'') := by
  let C : TranslationDomains.Cx.{u} :=
    { R := R, Y := Y, y := y, U := U, m := m, hU₁ := hU₁, hU₂ := hU₂, hΦ := hΦ, hΦ₂ := hΦ₂, hΨ
      := hΨ,
      hassoc := hassoc, hUK := hUK, R' := R', Y' := Y', y' := y', ι := ι, U' := U', m' := m',
        hext := hext,
      hstat := hstat }
  obtain ⟨D, hle, M, hM, hsq⟩ := C.exists_extension
  have h :=
    isOpenImmersion_lift_and_forall_comp_eq_of_homOfLE_comp_eq_of_forall_dense_preimage_fibre
      y' U' m' hU'₁ hU'₂ hΦ' hΦ'₁ hΦ'₂ hΨ' hΨ'₁ hΨ'₂ hassoc' D hle M hM
  exact ⟨D, hle, M, hM, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2, hsq⟩


end NeronModelInfra

namespace AbelianVarieties.NOSProofs.EtaleTranslationDomains
end AbelianVarieties.NOSProofs.EtaleTranslationDomains
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_etale_translation_extension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.EtaleTranslationExtensions


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace TranslationRefinement

open NeronModelInfra renaming
 exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre
 → glueTranslation

section Algebra

theorem specMap_apply_ne_closedPoint {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B]
  [IsDomain B]
    [IsLocalRing B] [Ring.DimensionLEOne B] (hA : IsLocalRing.maximalIdeal A ≠ ⊥) (f : A →+* B)
    (hf : Function.Injective f) (p : ↥(Spec (CommRingCat.of B))) (hp : p ≠
      IsLocalRing.closedPoint B) :
    (Spec.map (CommRingCat.ofHom f)).base p ≠ IsLocalRing.closedPoint A := by
  have hbot : p.asIdeal = ⊥ := by
    by_contra h
    exact hp (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal p.isPrime
      h)))
  intro h
  have h' : (PrimeSpectrum.comap f p).asIdeal = IsLocalRing.maximalIdeal A := by
    exact congrArg PrimeSpectrum.asIdeal h
  change p.asIdeal.comap f = IsLocalRing.maximalIdeal A at h'
  rw [hbot, Ideal.comap_bot_of_injective f hf] at h'
  exact hA h'.symm

theorem exists_ringHom_comp_eq {A B K : Type u} [CommRing A] [IsLocalRing A] [CommRing B]
  [IsLocalRing B]
    [Algebra A B] [Module.Finite A B] [Field K] [IsAlgClosed K]
    (φ : A →+* K) (hφ : ∀ x ∈ IsLocalRing.maximalIdeal A, φ x = 0) :
    ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = φ ∧ ∀ x ∈ IsLocalRing.maximalIdeal B, ψ x = 0 := by
  classical
  have : IsLocalHom (algebraMap A B) := by
    refine ⟨fun x hx => ?_⟩
    by_contra hxu
    have hxm : x ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal x).mpr hxu
    have hmax : (Ideal.comap (algebraMap A B) (IsLocalRing.maximalIdeal B)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) (IsLocalRing.maximalIdeal B)
    have heq := IsLocalRing.eq_maximalIdeal hmax
    have : algebraMap A B x ∈ IsLocalRing.maximalIdeal B := by
      rw [← Ideal.mem_comap, heq]; exact hxm
    exact (IsLocalRing.mem_maximalIdeal _).mp this hx
  have : IsLocalHom φ := by
    refine ⟨fun x hx => ?_⟩
    by_contra hxu
    have := hφ x ((IsLocalRing.mem_maximalIdeal x).mpr hxu)
    rw [this] at hx
    exact not_isUnit_zero hx
  let φ' : IsLocalRing.ResidueField A →+* K := IsLocalRing.ResidueField.lift φ
  let : Algebra (IsLocalRing.ResidueField A) K := φ'.toAlgebra
  have : Algebra.IsAlgebraic (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    Algebra.IsAlgebraic.of_finite _ _
  let ψ' : IsLocalRing.ResidueField B →ₐ[IsLocalRing.ResidueField A] K := IsAlgClosed.lift
  refine ⟨ψ'.toRingHom.comp (IsLocalRing.residue B), ?_, ?_⟩
  · ext x
    change ψ' (IsLocalRing.residue B (algebraMap A B x)) = φ x
    have h1 : IsLocalRing.residue B (algebraMap A B x) =
        algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
          (IsLocalRing.residue A x) := rfl
    rw [h1, ψ'.commutes]
    rfl
  · intro x hx
    change ψ' (IsLocalRing.residue B x) = 0
    rw [(IsLocalRing.residue_eq_zero_iff x).mpr hx, map_zero]

end Algebra

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {Y : Scheme.{u}} {y : Y ⟶ Spec (CommRingCat.of R)}
variable {U : (pullback y y).Opens} {m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y}

variable (y U m) in
/-- The density and associativity properties of the partial group law. -/
structure Strict : Prop where
  /-- Density along the first projection. -/
  hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback
        y y)) ⁻¹'
          (U : Set ↑(pullback y y)))
  /-- Density along the second projection. -/
  hU₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback
        y y)) ⁻¹'
          (U : Set ↑(pullback y y)))
  /-- The first translation map is an open immersion. -/
  hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm))
  /-- Density of the first translation image along the first projection. -/
  hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback
        y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base))
  /-- Density of the first translation image along the second projection. -/
  hΦ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback
        y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base))
  /-- The second translation map is an open immersion. -/
  hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition])))
  /-- Density of the second translation image along the first projection. -/
  hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback
        y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base))
  /-- Density of the second translation image along the second projection. -/
  hΨ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback
        y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base))
  /-- Associativity on the common domain. -/
  hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫
        pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y
        = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1
  /-- The generic fiber is contained in the multiplication domain. -/
  hUK : ∀ q : ↑(pullback y y), (pullback.fst y y ≫ y).base q ≠ IsLocalRing.closedPoint R → q ∈ U

variable (y U m) in
/-- A finite étale refinement of the partial group model. -/
structure Level (K : Type u) [Field K] (φ₀ : R →+* K) : Type (u + 1) where
  /-- The finite étale extension ring. -/
  R' : Type u
  /-- The commutative ring structure of the extension. -/
  [cr : CommRing R']
  /-- The base is a domain. -/
  [dom : IsDomain R']
  /-- The base is a discrete valuation ring. -/
  [dvr : IsDiscreteValuationRing R']
  /-- The algebra structure of the base extension. -/
  [alg : Algebra R R']
  /-- The base extension is finite as a module. -/
  [fin : Module.Finite R R']
  /-- The base extension is étale. -/
  [et : Algebra.Etale R R']
  /-- The base extension is faithfully flat. -/
  [ff : Module.FaithfullyFlat R R']
  /-- The chosen map to the algebraically closed residue extension. -/
  φ : R' →+* K
  /-- The chosen residue map extends the original one. -/
  hφ : φ.comp (algebraMap R R') = φ₀
  /-- The residue map kills the maximal ideal. -/
  hφm : ∀ x ∈ IsLocalRing.maximalIdeal R', φ x = 0
  /-- The refined model. -/
  Y' : Scheme.{u}
  /-- The structure morphism of the refined model. -/
  y' : Y' ⟶ Spec (CommRingCat.of R')
  /-- Smoothness of the refined model. -/
  [sm : Smooth y']
  /-- Separatedness of the refined model. -/
  [sep : IsSeparated y']
  /-- Quasi-compactness of the refined model. -/
  [qc : QuasiCompact y']
  /-- The inclusion of the base-changed original model. -/
  ι : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y'
  /-- The inclusion is an open immersion. -/
  [oi : IsOpenImmersion ι.1]
  /-- The inclusion contains the generic fiber. -/
  hgen : ∀ p : Y', y'.base p ≠ IsLocalRing.closedPoint R' → p ∈ Set.range ι.1.base
  /-- The inclusion contains all maximal generalizations in fibers. -/
  hmax : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base
  /-- The refined domain of partial multiplication. -/
  U' : (pullback y' y').Opens
  /-- The refined partial multiplication. -/
  m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y'
  /-- Compatibility of the refined partial multiplication. -/
  hU'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y')))
  /-- Compatibility of the refined partial multiplication. -/
  hU'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y')))
  /-- The first translation map is an open immersion. -/
  hΦ' : IsOpenImmersion
      (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm))
  /-- Compatibility of the refined partial multiplication. -/
  hΦ'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))
  /-- Compatibility of the refined partial multiplication. -/
  hΦ'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))
  /-- The second translation map is an open immersion. -/
  hΨ' : IsOpenImmersion
      (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition])))
  /-- Compatibility of the refined partial multiplication. -/
  hΨ'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))
  /-- Compatibility of the refined partial multiplication. -/
  hΨ'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))
  /-- Associativity on the common domain. -/
  hassoc' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
        (u v p q : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y')),
      u.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.fst y' y' →
      p.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 → p.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫
        U'.ι ≫ pullback.snd y' y' →
      q.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U'.ι ≫ pullback.fst y' y' → q.1 ≫ U'.ι ≫
        pullback.snd y' y' = v.1 ≫ m'.1 →
      p.1 ≫ m'.1 = q.1 ≫ m'.1
  /-- Compatibility with the original partial multiplication. -/
  hext : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫
          pullback.fst y y ≫ y))
        (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y),
      a.1 = w.1 ≫ U.ι ≫ pullback.fst y y → b.1 = w.1 ≫ U.ι ≫ pullback.snd y y → c.1 = w.1 ≫ m.1 →
      ∃ w' : SchemeHomOver t' (U'.ι ≫ pullback.fst y' y' ≫ y'),
        w'.1 ≫ U'.ι ≫ pullback.fst y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map
          (CommRingCat.ofHom (algebraMap R R'))) a).1 ≫ ι.1 ∧
        w'.1 ≫ U'.ι ≫ pullback.snd y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map
          (CommRingCat.ofHom (algebraMap R R'))) b).1 ≫ ι.1 ∧
        w'.1 ≫ m'.1 = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom
          (algebraMap R R'))) c).1 ≫ ι.1

variable {K : Type u} [Field K] {φ₀ : R →+* K}

attribute [scoped instance] Level.cr Level.dom Level.dvr Level.alg Level.fin Level.et
  Level.ff Level.sm Level.sep Level.qc Level.oi

namespace Level

variable (E : Level y U m K φ₀)

/-- The finite étale base morphism. -/
noncomputable abbrev s : Spec (CommRingCat.of E.R') ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R E.R'))

/-- The pair scheme over the refined base. -/
noncomputable abbrev X : Scheme.{u} := pullback (pullback.fst y y ≫ y) E.s

/-- The projection from the refined pair scheme. -/
noncomputable abbrev prX : E.X ⟶ pullback y y := pullback.fst (pullback.fst y y ≫ y) E.s

/-- The known domain of multiplication after base extension. -/
noncomputable abbrev UX : E.X.Opens := E.prX ⁻¹ᵁ U

/-- The multiplication morphism on the known domain. -/
noncomputable def hom : (E.UX : Scheme.{u}) ⟶ E.Y' :=
  pullback.lift (f := y) (g := E.s) (E.prX.resLE U E.UX le_rfl ≫ m.1) (E.UX.ι ≫ pullback.snd _ _)
    (by rw [Category.assoc, m.2, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
      Category.assoc,
          pullback.condition]) ≫ E.ι.1

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem hom_comp_y' : E.hom ≫ E.y' = E.UX.ι ≫ pullback.snd (pullback.fst y y ≫ y) E.s := by
  rw [hom, Category.assoc, E.ι.2, pullback.lift_snd]

theorem s_apply_ne_closedPoint (p : ↥(Spec (CommRingCat.of E.R'))) (hp : p ≠
  IsLocalRing.closedPoint E.R') :
    E.s.base p ≠ IsLocalRing.closedPoint R :=
  specMap_apply_ne_closedPoint (IsDiscreteValuationRing.not_a_field R) _
    (FaithfulSMul.algebraMap_injective R E.R') p hp

theorem mem_UX_of_ne (hS : Strict y U m) (q : ↥E.X)
    (hq : (pullback.snd (pullback.fst y y ≫ y) E.s).base q ≠ IsLocalRing.closedPoint E.R') : q ∈
      E.UX := by
  change E.prX.base q ∈ U
  apply hS.hUK
  have h := congrArg (fun f => f.base q) (pullback.condition (f := pullback.fst y y ≫ y) (g :=
    E.s))
  simp only [Scheme.Hom.comp_apply] at h
  rw [show (pullback.fst y y ≫ y).base (E.prX.base q) = y.base ((pullback.fst y y).base
    (E.prX.base q)) from
    Scheme.Hom.comp_apply _ _ _, h]
  exact E.s_apply_ne_closedPoint _ hq

variable [Smooth y]

scoped instance smooth_sndX : Smooth (pullback.snd (pullback.fst y y ≫ y) E.s) :=
  MorphismProperty.of_isPullback (P := (@Smooth : MorphismProperty Scheme.{u}))
    (IsPullback.of_hasPullback (pullback.fst y y ≫ y) E.s) inferInstance

theorem dense_UX (hS : Strict y U m) : Dense (E.UX : Set ↥E.X) := by
  intro q
  have hgen := Flat.generalizingMap (pullback.snd (pullback.fst y y ≫ y) E.s)
  let η : ↥(Spec (CommRingCat.of E.R')) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum E.R')
  have hη : η ⤳ (pullback.snd (pullback.fst y y ≫ y) E.s).base q :=
    (PrimeSpectrum.le_iff_specializes _ _).mp (show η.asIdeal ≤ _ from bot_le)
  obtain ⟨q', hq', hq'η⟩ := hgen hη
  have hne : η ≠ IsLocalRing.closedPoint E.R' := by
    intro h
    have := congrArg PrimeSpectrum.asIdeal h
    exact IsDiscreteValuationRing.not_a_field E.R' (this.symm.trans rfl)
  have hq'U : q' ∈ E.UX := E.mem_UX_of_ne hS q' (fun h => hne (hq'η.symm.trans h))
  exact closure_mono (Set.singleton_subset_iff.mpr hq'U) (specializes_iff_mem_closure.mp hq')

scoped instance isReduced_X : IsReduced E.X :=
  AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (pullback.snd
    (pullback.fst y y ≫ y) E.s)

scoped instance isSeparated_Y' : E.Y'.IsSeparated := by
  rw [Scheme.isSeparated_iff, ← terminal.comp_from E.y']
  infer_instance

/-- The partial multiplication map determined by the dense domain. -/
noncomputable def pm (hS : Strict y U m) : E.X.PartialMap E.Y' := ⟨E.UX, E.dense_UX hS, E.hom⟩

/-- The maximal domain of the induced rational map. -/
noncomputable def D (hS : Strict y U m) : E.X.Opens := (E.pm hS).toRationalMap.domain

/-- The extension of multiplication to its maximal domain. -/
noncomputable def M (hS : Strict y U m) : ((E.D hS : E.X.Opens) : Scheme.{u}) ⟶ E.Y' :=
  ((E.pm hS).toRationalMap.toPartialMap).hom

theorem UX_le_D (hS : Strict y U m) : E.UX ≤ E.D hS := (E.pm hS).le_domain_toRationalMap

theorem homOfLE_M (hS : Strict y U m) : E.X.homOfLE (E.UX_le_D hS) ≫ E.M hS = E.hom := by
  have h := (E.pm hS).toPartialMap_toRationalMap_restrict
  exact h

theorem le_D_of_hom (hS : Strict y U m) (V : E.X.Opens) (hUV : E.UX ≤ V) (g : (V : Scheme.{u}) ⟶
  E.Y')
    (hg : E.X.homOfLE hUV ≫ g = E.hom) : V ≤ E.D hS := by
  let g' : E.X.PartialMap E.Y' := ⟨V, (E.dense_UX hS).mono hUV, g⟩
  have heq : g'.toRationalMap = (E.pm hS).toRationalMap := by
    rw [Scheme.PartialMap.toRationalMap_eq_iff]
    refine ⟨E.UX, E.dense_UX hS, hUV, le_rfl, ?_⟩
    simp only [Scheme.PartialMap.restrict_hom, g', pm, hg, Scheme.homOfLE_rfl,
      Category.id_comp]
    rfl
  have := g'.le_domain_toRationalMap
  rw [heq] at this
  exact this

scoped instance isReduced_D (hS : Strict y U m) : IsReduced ((E.D hS : E.X.Opens) : Scheme.{u})
  := inferInstance

theorem M_comp_y' (hS : Strict y U m) :
    E.M hS ≫ E.y' = (E.D hS).ι ≫ pullback.snd (pullback.fst y y ≫ y) E.s := by
  have : IsDominant (E.X.homOfLE (E.UX_le_D hS)) := Opens.isDominant_homOfLE (E.dense_UX hS) _
  apply ext_of_isDominant (E.X.homOfLE (E.UX_le_D hS))
  rw [← Category.assoc, E.homOfLE_M, hom_comp_y', ← Category.assoc, Scheme.homOfLE_ι]

/-- The geometric special fiber of the pair scheme. -/
noncomputable abbrev Ω (y : Y ⟶ Spec (CommRingCat.of R)) (φ₀ : R →+* K) : Scheme.{u} :=
  pullback (pullback.fst y y ≫ y) (Spec.map (CommRingCat.ofHom φ₀))

omit [IsDomain R] [IsDiscreteValuationRing R] [Smooth y] in
theorem specMap_φ_comp_s : Spec.map (CommRingCat.ofHom E.φ) ≫ E.s = Spec.map (CommRingCat.ofHom
  φ₀) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, E.hφ]

/-- The comparison from the geometric special fiber to a refinement. -/
noncomputable def ρ : Ω y φ₀ ⟶ E.X :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom E.φ)) (𝟙 _)
    (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, E.specMap_φ_comp_s])

/-- The closed locus where the refined multiplication is undefined. -/
def Z (hS : Strict y U m) : Set ↥(Ω y φ₀) := E.ρ.base ⁻¹' (E.D hS : Set ↥E.X)ᶜ

theorem isClosed_Z (hS : Strict y U m) : IsClosed (E.Z hS) :=
  ((E.D hS).isOpen.isClosed_compl).preimage E.ρ.base.hom.continuous

section Stat

variable {R'' : Type u} [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra
  E.R' R'']

/-- The morphism of spectra for a further base extension. -/
noncomputable abbrev t (R'' : Type u) [CommRing R''] [Algebra E.R' R''] :
    Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of E.R') :=
  Spec.map (CommRingCat.ofHom (algebraMap E.R' R''))

/-- The pair scheme for the extended model. -/
noncomputable def P (s : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R)) (hs : s = E.t R''
  ≫ E.s)
    (a : Spec (CommRingCat.of R'') ⟶ Y) (ha : a ≫ y = s) : pullback y s ⟶ E.X :=
  pullback.lift (f := pullback.fst y y ≫ y) (g := E.s)
    (pullback.lift (f := y) (g := y) (pullback.snd y s ≫ a) (pullback.fst y s)
      (by rw [Category.assoc, ha, pullback.condition]))
    (pullback.snd y s ≫ E.t R'')
    (by rw [pullback.lift_fst_assoc, Category.assoc, ha, Category.assoc, ← hs])

omit [IsDomain R] [IsDiscreteValuationRing R] [Smooth y]
  [IsDomain R''] [IsDiscreteValuationRing R''] in
@[reassoc (attr := simp)]
theorem P_prX (s : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R)) (hs : s = E.t R'' ≫ E.s)
    (a : Spec (CommRingCat.of R'') ⟶ Y) (ha : a ≫ y = s) :
    E.P s hs a ha ≫ E.prX = pullback.lift (f := y) (g := y) (pullback.snd y s ≫ a) (pullback.fst
      y s)
      (by rw [Category.assoc, ha, pullback.condition]) :=
  pullback.lift_fst _ _ _

omit [IsDomain R] [IsDiscreteValuationRing R] [Smooth y]
  [IsDomain R''] [IsDiscreteValuationRing R''] in
@[reassoc (attr := simp)]
theorem P_snd (s : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R)) (hs : s = E.t R'' ≫ E.s)
    (a : Spec (CommRingCat.of R'') ⟶ Y) (ha : a ≫ y = s) :
    E.P s hs a ha ≫ pullback.snd (pullback.fst y y ≫ y) E.s = pullback.snd y s ≫ E.t R'' :=
  pullback.lift_snd _ _ _

/-- Existence of a translation compatible with the partial multiplication. -/
def Stat (s : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R)) (a : Spec (CommRingCat.of
  R'') ⟶ Y) : Prop :=
  ∃ τ : pullback y s ⟶ pullback E.y' (E.t R''),
    τ ≫ pullback.snd E.y' (E.t R'') = pullback.snd y s ∧
    ∀ {T : Scheme.{u}} (x : T ⟶ pullback y s) (w : T ⟶ (U : Scheme.{u})) (v : T ⟶ pullback y E.s),
      w ≫ U.ι ≫ pullback.fst y y = x ≫ pullback.snd y s ≫ a →
      w ≫ U.ι ≫ pullback.snd y y = x ≫ pullback.fst y s →
      v ≫ pullback.fst y E.s = w ≫ m.1 →
      v ≫ pullback.snd y E.s = x ≫ pullback.snd y s ≫ E.t R'' →
      x ≫ τ ≫ pullback.fst E.y' (E.t R'') = v ≫ E.ι.1

omit [IsDomain R''] [IsDiscreteValuationRing R''] in
theorem stat_of_range_subset (hS : Strict y U m)
    (s : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R)) (hs : s = E.t R'' ≫ E.s)
    (a : Spec (CommRingCat.of R'') ⟶ Y) (ha : a ≫ y = s)
    (hP : Set.range (E.P s hs a ha).base ⊆ (E.D hS : Set ↥E.X)) : E.Stat s a := by
  let P' : pullback y s ⟶ (E.D hS : Scheme.{u}) :=
    IsOpenImmersion.lift (E.D hS).ι (E.P s hs a ha) (by rwa [Scheme.Opens.range_ι])
  have hP' : P' ≫ (E.D hS).ι = E.P s hs a ha := IsOpenImmersion.lift_fac _ _ _
  let τ₀ : pullback y s ⟶ E.Y' := P' ≫ E.M hS
  have hτ₀ : τ₀ ≫ E.y' = pullback.snd y s ≫ E.t R'' := by
    rw [Category.assoc, E.M_comp_y', ← Category.assoc, hP', E.P_snd]
  refine ⟨pullback.lift τ₀ (pullback.snd y s) hτ₀, pullback.lift_snd _ _ _, ?_⟩
  intro T x w v h1 h2 h3 h4
  rw [pullback.lift_fst]
  have hxP : x ≫ E.P s hs a ha ≫ E.prX = w ≫ U.ι := by
    rw [E.P_prX]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]; exact h1.symm
    · rw [Category.assoc, pullback.lift_snd]; exact h2.symm
  have hrange : Set.range (x ≫ E.P s hs a ha).base ⊆ Set.range E.UX.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change E.prX.base ((x ≫ E.P s hs a ha).base z) ∈ U
    rw [← Scheme.Hom.comp_apply, Category.assoc, hxP, Scheme.Hom.comp_apply]
    exact (w.base z).2
  let x' : T ⟶ (E.UX : Scheme.{u}) := IsOpenImmersion.lift E.UX.ι (x ≫ E.P s hs a ha) hrange
  have hx' : x' ≫ E.UX.ι = x ≫ E.P s hs a ha := IsOpenImmersion.lift_fac _ _ _
  have hxP' : x ≫ P' = x' ≫ E.X.homOfLE (E.UX_le_D hS) := by
    rw [← cancel_mono (E.D hS).ι, Category.assoc, hP', Category.assoc, Scheme.homOfLE_ι, hx']
  have hw : x' ≫ E.prX.resLE U E.UX le_rfl = w := by
    rw [← cancel_mono U.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, hx',
      Category.assoc, hxP]
  have hv : x' ≫ pullback.lift (f := y) (g := E.s) (E.prX.resLE U E.UX le_rfl ≫ m.1) (E.UX.ι ≫
    pullback.snd _ _)
      (by rw [Category.assoc, m.2, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
        Category.assoc,
          pullback.condition]) = v := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hw, h3]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hx', Category.assoc, E.P_snd, h4]
  change x ≫ (P' ≫ E.M hS) = v ≫ E.ι.1
  rw [← Category.assoc, hxP', Category.assoc, E.homOfLE_M, hom, ← Category.assoc, hv]

omit [IsDomain R''] [IsDiscreteValuationRing R''] in
theorem exists_not_mem_D (hS : Strict y U m)
    (s : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R)) (hs : s = E.t R'' ≫ E.s)
    (a : Spec (CommRingCat.of R'') ⟶ Y) (ha : a ≫ y = s) (hn : ¬ E.Stat s a) :
    ∃ b : ↥(pullback y s), (E.P s hs a ha).base b ∉ E.D hS := by
  by_contra h
  push Not at h
  exact hn (E.stat_of_range_subset hS s hs a ha (by rintro _ ⟨b, rfl⟩; exact h b))

end Stat

/-- Existence of a section of the refined model. -/
def HasSec : Prop := ∃ a' : Spec (CommRingCat.of E.R') ⟶ E.Y', a' ≫ E.y' = 𝟙 _

section Next

variable [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y] [IsAlgClosed K]
variable {R'' : Type u} [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra
  E.R' R'']
  [Module.Finite E.R' R''] [Algebra.Etale E.R' R''] [Module.FaithfullyFlat E.R' R'']
  [Algebra R R''] [IsScalarTower R E.R' R'']
  [Module.Finite R R''] [Algebra.Etale R R''] [Module.FaithfullyFlat R R'']

omit [IsDomain R] [IsDiscreteValuationRing R] [Smooth y] [IsSeparated y]
  [LocallyOfFiniteType y] [QuasiCompact y] [IsAlgClosed K]
  [IsDomain R''] [IsDiscreteValuationRing R'']
  [Module.Finite E.R' R''] [Algebra.Etale E.R' R''] [Module.FaithfullyFlat E.R' R'']
  [Module.Finite R R''] [Algebra.Etale R R''] [Module.FaithfullyFlat R R''] in
theorem s₂_eq : Spec.map (CommRingCat.ofHom (algebraMap R R'')) = E.t R'' ≫ E.s := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]


omit [Algebra.Etale E.R' R''] in
theorem exists_next (hS : Strict y U m)
    (s : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R)) (hs : s = E.t R'' ≫ E.s)
    (a : Spec (CommRingCat.of R'') ⟶ Y) (ha : a ≫ y = s) :
    ∃ E₂ : Level y U m K φ₀, E₂.HasSec ∧ E₂.Z hS ⊆ E.Z hS ∧
      ∀ b : ↥(pullback y s), (E.P s hs a ha).base b ∉ E.D hS → E₂.Z hS ≠ E.Z hS := by
  obtain rfl : s = Spec.map (CommRingCat.ofHom (algebraMap R R'')) := hs.trans E.s₂_eq.symm
  obtain ⟨ψ, hψ, hψm⟩ := exists_ringHom_comp_eq (A := E.R') (B := R'') E.φ E.hφm
  obtain ⟨Y'', y'', ι₂, U'', m'', hsm, hsep, hloft, hqc, hoi, hgen₂, hmax₂, h1, h2, h3, h4, h5,
    h6, h7, h8,
      hassoc₂, hext₂, ⟨a'', ha''⟩, ⟨j, hj, hjy, hjc⟩, ⟨D₂, hle, M₂, hM₂, hprog⟩⟩ :=
    glueTranslation
      y U m hS.hU₁ hS.hU₂ hS.hΦ hS.hΦ₁ hS.hΦ₂ hS.hΨ hS.hΨ₁ hS.hΨ₂ hS.hassoc hS.hUK
      E.R' E.y' E.ι E.hgen E.hmax E.U' E.m' E.hU'₁ E.hU'₂ E.hΦ' E.hΦ'₁ E.hΦ'₂ E.hΨ' E.hΨ'₁
        E.hΨ'₂ E.hassoc' E.hext
      R'' a ha
  let E₂ : Level y U m K φ₀ :=
    { R' := R'', φ := ψ,
      hφ := by rw [IsScalarTower.algebraMap_eq R E.R' R'', ← RingHom.comp_assoc, hψ, E.hφ],
      hφm := hψm, Y' := Y'', y' := y'', sm := hsm, sep := hsep, qc := hqc, ι := ι₂, oi := hoi,
      hgen := hgen₂, hmax := hmax₂, U' := U'', m' := m'', hU'₁ := h1, hU'₂ := h2, hΦ' := h3,
        hΦ'₁ := h4, hΦ'₂ := h5,
      hΨ' := h6, hΨ'₁ := h7, hΨ'₂ := h8, hassoc' := hassoc₂, hext := hext₂ }
  have hE₂t : E₂.t R'' = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom (RingHom.id R'')) = 𝟙 _
    rw [CommRingCat.ofHom_id, Spec.map_id]
  let π : E₂.X ⟶ E.X := pullback.map _ _ _ _ (𝟙 _) (E.t R'') (𝟙 _)
      (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id]; exact hs)
  have hπ₁ : π ≫ E.prX = E₂.prX := by
    simp only [π, pullback.lift_fst, Category.comp_id]
  have hπ₂ : π ≫ pullback.snd _ E.s = pullback.snd _ E₂.s ≫ E.t R'' := by
    simp only [π, pullback.lift_snd]
  have hρ : E.ρ = E₂.ρ ≫ π := by
    apply pullback.hom_ext
    · simp only [Level.ρ, π, Category.assoc, pullback.lift_fst, Category.comp_id]
    · simp only [Level.ρ, π, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      change _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom
        (algebraMap E.R' R''))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
  have hUX : E₂.UX = π ⁻¹ᵁ E.UX := by
    change E₂.prX ⁻¹ᵁ U = π ⁻¹ᵁ (E.prX ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, hπ₁]
  let V : E₂.X.Opens := π ⁻¹ᵁ (E.D hS)
  have hUXV : E₂.UX ≤ V := by rw [hUX]; exact fun q hq => E.UX_le_D hS hq
  have hlift : (π.resLE (E.D hS) V le_rfl ≫ E.M hS) ≫ E.y' = (V.ι ≫ pullback.snd _ E₂.s) ≫ E.t
    R'' := by
    rw [Category.assoc, E.M_comp_y', ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
      hπ₂,
      Category.assoc]
  let g : (V : Scheme.{u}) ⟶ Y'' :=
    pullback.lift (π.resLE (E.D hS) V le_rfl ≫ E.M hS) (V.ι ≫ pullback.snd _ E₂.s) hlift ≫ j
  let κ : (E₂.UX : Scheme.{u}) ⟶ (E.UX : Scheme.{u}) := π.resLE E.UX E₂.UX (le_of_eq hUX)
  have hκ : κ ≫ E.UX.ι = E₂.UX.ι ≫ π := Scheme.Hom.resLE_comp_ι _ _
  have hκres : κ ≫ E.prX.resLE U E.UX le_rfl = E₂.prX.resLE U E₂.UX le_rfl := by
    rw [← cancel_mono U.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, hκ,
      Category.assoc, hπ₁,
      Scheme.Hom.resLE_comp_ι]
  have hcondE : (E.prX.resLE U E.UX le_rfl ≫ m.1) ≫ y = (E.UX.ι ≫ pullback.snd _ E.s) ≫ E.s := by
    rw [Category.assoc, m.2, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
      Category.assoc,
      pullback.condition]
  have hcond₂ : (E₂.prX.resLE U E₂.UX le_rfl ≫ m.1) ≫ y = (E₂.UX.ι ≫ pullback.snd _ E₂.s) ≫ E₂.s
    := by
    rw [Category.assoc, m.2, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
      Category.assoc,
      pullback.condition]
  have hg : E₂.X.homOfLE hUXV ≫ g = E₂.hom := by
    change _ = pullback.lift _ _ hcond₂ ≫ ι₂.1
    simp only [g, ← Category.assoc]
    refine hjc (pullback.lift _ _ hcond₂) (κ ≫ pullback.lift _ _ hcondE) _ ?_ ?_ ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc, hκres]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, ← Category.assoc, hκ,
      Category.assoc, hπ₂,
        Category.assoc]
    · rw [Category.assoc, pullback.lift_fst, Category.assoc]
      change _ = κ ≫ E.hom
      rw [← E.homOfLE_M hS, ← Category.assoc, ← Category.assoc]
      congr 1
      rw [← cancel_mono (E.D hS).ι, Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι,
        Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι, hκ]
    · rw [Category.assoc, pullback.lift_snd, Scheme.homOfLE_ι_assoc, pullback.lift_snd]
  have hVD : V ≤ E₂.D hS := E₂.le_D_of_hom hS V hUXV g hg
  have hmono : E₂.Z hS ⊆ E.Z hS := by
    intro ω hω hω'
    apply hω
    apply hVD
    change π.base (E₂.ρ.base ω) ∈ (E.D hS : Set ↥E.X)
    rw [← Scheme.Hom.comp_apply, ← hρ]
    simpa only [Level.Z, Set.mem_preimage, Set.mem_compl_iff, not_not] using hω'
  refine ⟨E₂, ⟨a'', ha''⟩, hmono, ?_⟩
  intro b hb heq
  have hs₂ : Spec.map (CommRingCat.ofHom (algebraMap R R'')) = E₂.t R'' ≫ E₂.s := by
    rw [hE₂t, Category.id_comp]
  let P₂ : pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) ⟶ E₂.X := E₂.P _ hs₂ a ha
  have hP₂π : P₂ ≫ π = E.P _ hs a ha := by
    apply pullback.hom_ext
    · rw [Category.assoc, hπ₁, E₂.P_prX, E.P_prX]
    · rw [Category.assoc, hπ₂, E₂.P_snd_assoc, E.P_snd, hE₂t, Category.id_comp]
  let θ₁ : E₂.X ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) :=
    pullback.lift (E₂.prX ≫ pullback.fst y y) (pullback.snd _ E₂.s) (by rw [Category.assoc]; exact
      pullback.condition)
  let θ₂ : E₂.X ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) :=
    pullback.lift (E₂.prX ≫ pullback.snd y y) (pullback.snd _ E₂.s)
      (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition)
  have hθ : (θ₁ ≫ ι₂.1) ≫ y'' = (θ₂ ≫ ι₂.1) ≫ y'' := by
    simp only [Category.assoc, ι₂.2, θ₁, θ₂, pullback.lift_snd]
  let κ₂ : E₂.X ⟶ pullback y'' y'' := pullback.lift (θ₁ ≫ ι₂.1) (θ₂ ≫ ι₂.1) hθ
  let a₂ : Spec (CommRingCat.of R'') ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R
    R''))) :=
    pullback.lift a (𝟙 _) (by rw [Category.id_comp]; exact ha)
  have hq₁ : (P₂ ≫ κ₂) ≫ pullback.fst y'' y'' =
      𝟙 _ ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) ≫ a₂ ≫ ι₂.1 := by
    rw [Category.id_comp, Category.assoc, pullback.lift_fst, ← Category.assoc, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, E₂.P_prX_assoc, pullback.lift_fst, Category.assoc,
      pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, E₂.P_snd, Category.assoc, pullback.lift_snd, hE₂t]
  have hq₂ : (P₂ ≫ κ₂) ≫ pullback.snd y'' y'' = 𝟙 _ ≫ ι₂.1 := by
    rw [Category.id_comp, Category.assoc, pullback.lift_snd, ← Category.assoc]
    conv_rhs => rw [← Category.id_comp ι₂.1]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, E₂.P_prX_assoc, pullback.lift_snd, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, E₂.P_snd, hE₂t, Category.id_comp, Category.comp_id]
  have hrange := hprog a₂ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (𝟙 _) (P₂ ≫ κ₂)
    hq₁ hq₂
  have hbD₂ : κ₂.base (P₂.base b) ∈ (D₂ : Set ↥(pullback y'' y'')) :=
    hrange ⟨b, (Scheme.Hom.comp_apply _ _ _).symm⟩
  let V₂ : E₂.X.Opens := κ₂ ⁻¹ᵁ D₂
  let t' : (E₂.UX : Scheme.{u}) ⟶ Spec (CommRingCat.of R'') := E₂.UX.ι ≫ pullback.snd _ E₂.s
  have hw : (E₂.prX.resLE U E₂.UX le_rfl ≫ U.ι ≫ pullback.fst y y ≫ y) =
      t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'')) := by
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, pullback.condition,
      Category.assoc]
  have hwa : (E₂.prX.resLE U E₂.UX le_rfl ≫ U.ι ≫ pullback.fst y y) ≫ y =
      t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'')) := by
    simp only [Category.assoc]; exact hw
  have hwb : (E₂.prX.resLE U E₂.UX le_rfl ≫ U.ι ≫ pullback.snd y y) ≫ y =
      t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'')) := by
    simp only [Category.assoc]; rw [← pullback.condition (f := y) (g := y)]; exact hw
  have hwc : (E₂.prX.resLE U E₂.UX le_rfl ≫ m.1) ≫ y = t' ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R R'')) := by
    rw [Category.assoc, m.2]; exact hw
  let wpt : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R''))) (U.ι ≫
    pullback.fst y y ≫ y) :=
    ⟨E₂.prX.resLE U E₂.UX le_rfl, hw⟩
  let apt : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R''))) y := ⟨_, hwa⟩
  let bpt : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R''))) y := ⟨_, hwb⟩
  let cpt : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R''))) y := ⟨_, hwc⟩
  obtain ⟨w', hw'₁, hw'₂, hw'₃⟩ := hext₂ t' wpt apt bpt cpt rfl rfl rfl
  have hθ₁ : E₂.UX.ι ≫ θ₁ =
      (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'')))
        apt).1 := by
    rw [RelativeGroupLaw.baseChangePointOfBase_coe]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      change E₂.UX.ι ≫ E₂.prX ≫ pullback.fst y y = (E₂.prX.resLE U E₂.UX le_rfl ≫ U.ι) ≫
        pullback.fst y y
      rw [Scheme.Hom.resLE_comp_ι, Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have hθ₂ : E₂.UX.ι ≫ θ₂ =
      (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'')))
        bpt).1 := by
    rw [RelativeGroupLaw.baseChangePointOfBase_coe]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      change E₂.UX.ι ≫ E₂.prX ≫ pullback.snd y y = (E₂.prX.resLE U E₂.UX le_rfl ≫ U.ι) ≫
        pullback.snd y y
      rw [Scheme.Hom.resLE_comp_ι, Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have hκ₂ : E₂.UX.ι ≫ κ₂ = w'.1 ≫ U''.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hθ₁, Category.assoc, hw'₁]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hθ₂, Category.assoc, hw'₂]
  have hUXV₂ : E₂.UX ≤ V₂ := by
    intro q hq
    change κ₂.base q ∈ (D₂ : Set ↥(pullback y'' y''))
    apply hle
    let q' : ↥(E₂.UX : Scheme.{u}) := ⟨q, hq⟩
    have hq' : κ₂.base q = U''.ι (w'.1 q') := congrArg (fun f => f q') hκ₂
    rw [hq']
    exact (w'.1 q').2
  let g₂ : (V₂ : Scheme.{u}) ⟶ Y'' := κ₂.resLE D₂ V₂ le_rfl ≫ M₂.1
  have hg₂ : E₂.X.homOfLE hUXV₂ ≫ g₂ = E₂.hom := by
    have hww : E₂.X.homOfLE hUXV₂ ≫ κ₂.resLE D₂ V₂ le_rfl = w'.1 ≫ (pullback y'' y'').homOfLE
      hle := by
      rw [← cancel_mono D₂.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc, hκ₂,
        Category.assoc, Scheme.homOfLE_ι]
    simp only [g₂, ← Category.assoc, hww]
    rw [Category.assoc, hM₂, hw'₃, RelativeGroupLaw.baseChangePointOfBase_coe]
    change _ = pullback.lift _ _ hcond₂ ≫ ι₂.1
    rfl
  have hV₂D : V₂ ≤ E₂.D hS := E₂.le_D_of_hom hS V₂ hUXV₂ g₂ hg₂
  have hbD : P₂.base b ∈ (E₂.D hS : Set ↥E₂.X) := hV₂D hbD₂
  have hbcl : (pullback.snd _ E₂.s).base (P₂.base b) = IsLocalRing.closedPoint R'' := by
    by_contra hne
    apply hb
    apply E.UX_le_D hS
    change E.prX.base ((E.P _ hs a ha).base b) ∈ U
    rw [← hP₂π, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ E.prX, hπ₁]
    exact E₂.mem_UX_of_ne hS _ hne
  have : IsLocalHom (CommRingCat.ofHom ψ).hom := by
    refine ⟨fun x hx => ?_⟩
    by_contra hxu
    have := hψm x ((IsLocalRing.mem_maximalIdeal x).mpr hxu)
    rw [show (CommRingCat.ofHom ψ).hom x = ψ x from rfl, this] at hx
    exact not_isUnit_zero hx
  have hpt : (pullback.snd _ E₂.s).base (P₂.base b) =
      (Spec.map (CommRingCat.ofHom ψ)).base (IsLocalRing.closedPoint K) := by
    rw [hbcl]
    exact (Spec_closedPoint (R := CommRingCat.of R'') (S := CommRingCat.of K) (f :=
      CommRingCat.ofHom ψ)).symm
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd _ E₂.s)
    (g := Spec.map (CommRingCat.ofHom ψ)) (P₂.base b) (IsLocalRing.closedPoint K) hpt
  let lam : pullback (pullback.snd _ E₂.s) (Spec.map (CommRingCat.ofHom ψ)) ⟶ Ω y φ₀ :=
    pullback.lift (pullback.fst _ _ ≫ E₂.prX) (pullback.snd _ _)
      (by rw [Category.assoc, pullback.condition (f := pullback.fst y y ≫ y) (g := E₂.s), ←
        Category.assoc,
            pullback.condition (f := pullback.snd (pullback.fst y y ≫ y) E₂.s) (g := Spec.map
              (CommRingCat.ofHom ψ)),
            Category.assoc]
          exact congrArg (pullback.snd _ _ ≫ ·) E₂.specMap_φ_comp_s)
  have hlam : lam ≫ E₂.ρ = pullback.fst _ _ := by
    apply pullback.hom_ext
    · simp only [lam, Level.ρ, Category.assoc, pullback.lift_fst, Category.comp_id]
    · simp only [lam, Level.ρ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      exact pullback.condition.symm
  let ω : ↥(Ω y φ₀) := lam.base z
  have hω₂ : E₂.ρ.base ω = P₂.base b := by
    change (lam ≫ E₂.ρ).base z = _
    rw [hlam]; exact hz₁
  have hωE : E.ρ.base ω = (E.P _ hs a ha).base b := by
    rw [hρ, Scheme.Hom.comp_apply, hω₂, ← Scheme.Hom.comp_apply, hP₂π]
  have h₁ : ω ∈ E.Z hS := by
    change E.ρ.base ω ∈ (E.D hS : Set ↥E.X)ᶜ
    rw [hωE]; exact hb
  have h₂ : ω ∉ E₂.Z hS := by
    change ¬ (E₂.ρ.base ω ∈ (E₂.D hS : Set ↥E₂.X)ᶜ)
    rw [hω₂]; exact fun h => h hbD
  exact h₂ (heq ▸ h₁)

end Next

end Level

attribute [scoped instance] Level.smooth_sndX Level.isReduced_X Level.isSeparated_Y'
  Level.isReduced_D

section Final

variable [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem s₀_eq_id : Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 (Spec (CommRingCat.of R))
  := by
  change Spec.map (CommRingCat.ofHom (RingHom.id R)) = 𝟙 _
  rw [CommRingCat.ofHom_id, Spec.map_id]

private noncomputable def base (hS : Strict y U m) (hφ₀m : ∀ x ∈ IsLocalRing.maximalIdeal R, φ₀
  x = 0) :
    Level y U m K φ₀ where
  R' := R
  φ := φ₀
  hφ := RingHom.comp_id _
  hφm := hφ₀m
  Y' := Y
  y' := y
  ι := ⟨pullback.fst y _, by rw [pullback.condition, s₀_eq_id, Category.comp_id]⟩
  oi := by
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R R))) := by
      rw [s₀_eq_id]
      infer_instance
    exact MorphismProperty.pullback_fst (P := (@IsOpenImmersion : MorphismProperty Scheme.{u})) _
      _ this
  hgen := fun p _ => by
    have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R R))) := by
      rw [s₀_eq_id]
      infer_instance
    exact (MorphismProperty.of_isPullback
      (P := (@Surjective : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback y _).flip this).surj p
  hmax := fun p _ => by
    have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R R))) := by
      rw [s₀_eq_id]
      infer_instance
    exact (MorphismProperty.of_isPullback
      (P := (@Surjective : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback y _).flip this).surj p
  U' := U
  m' := m
  hU'₁ := hS.hU₁
  hU'₂ := hS.hU₂
  hΦ' := hS.hΦ
  hΦ'₁ := hS.hΦ₁
  hΦ'₂ := hS.hΦ₂
  hΨ' := hS.hΨ
  hΨ'₁ := hS.hΨ₁
  hΨ'₂ := hS.hΨ₂
  hassoc' := hS.hassoc
  hext := by
    intro T t' w a b c ha hb hc
    refine ⟨⟨w.1, by rw [w.2, s₀_eq_id, Category.comp_id]⟩, ?_, ?_, ?_⟩
    · rw [RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]; exact ha.symm
    · rw [RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]; exact hb.symm
    · rw [RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]; exact hc.symm

end Final

end Main

theorem main
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hS : Strict y U m) (hYk : ∃ x : Y, y.base x = IsLocalRing.closedPoint R) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ :
      Algebra R R')
      (_ : Module.Finite R R') (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R')
      (Y' : Scheme.{u}) (y' : Y' ⟶ Spec (CommRingCat.of R'))
      (ι : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y')
      (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y'),
      Smooth y' ∧ IsSeparated y' ∧ LocallyOfFiniteType y' ∧ QuasiCompact y' ∧
      IsOpenImmersion ι.1 ∧
      (∀ p : Y', y'.base p ≠ IsLocalRing.closedPoint R' → p ∈ Set.range ι.1.base) ∧
      (∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y')))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y')))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
          (u v p q : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y')),
        u.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.fst y' y' →
        p.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 →
        p.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.snd y' y' →
        q.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U'.ι ≫ pullback.fst y' y' →
        q.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ m'.1 →
        p.1 ≫ m'.1 = q.1 ≫ m'.1) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
          (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫
            pullback.fst y y ≫ y))
          (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y),
        a.1 = w.1 ≫ U.ι ≫ pullback.fst y y → b.1 = w.1 ≫ U.ι ≫ pullback.snd y y → c.1 = w.1 ≫ m.1 →
        ∃ w' : SchemeHomOver t' (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map
            (CommRingCat.ofHom (algebraMap R R'))) a).1 ≫ ι.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map
            (CommRingCat.ofHom (algebraMap R R'))) b).1 ≫ ι.1 ∧
          w'.1 ≫ m'.1 = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom
            (algebraMap R R'))) c).1 ≫ ι.1) ∧
      (∃ a' : Spec (CommRingCat.of R') ⟶ Y', a' ≫ y' = 𝟙 _) ∧
      (∀ (R'' : Type u) (_ : CommRing R'') (_ : IsDomain R'') (_ : IsDiscreteValuationRing R'')
          (_ : Algebra R' R'') (_ : Module.Finite R' R'') (_ : Algebra.Etale R' R'') (_ :
            Module.FaithfullyFlat R' R'')
          (a : Spec (CommRingCat.of R'') ⟶ Y),
        a ≫ y = (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map
          (CommRingCat.ofHom (algebraMap R R'))) →
        ∃ τ : pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map
          (CommRingCat.ofHom (algebraMap R R')))) ⟶ pullback y' (Spec.map (CommRingCat.ofHom
            (algebraMap R' R''))),
          τ ≫ pullback.snd y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = pullback.snd
            y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom
              (algebraMap R R')))) ∧
          ∀ {T : Scheme.{u}} (x : T ⟶ pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R'
            R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))))
            (w : T ⟶ (U : Scheme.{u})) (v : T ⟶ pullback y (Spec.map (CommRingCat.ofHom
              (algebraMap R R')))),
            w ≫ U.ι ≫ pullback.fst y y = x ≫ pullback.snd y ((Spec.map (CommRingCat.ofHom
              (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ a →
            w ≫ U.ι ≫ pullback.snd y y = x ≫ pullback.fst y ((Spec.map (CommRingCat.ofHom
              (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) →
            v ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ m.1 →
            v ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = x ≫
              pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map
                (CommRingCat.ofHom (algebraMap R R')))) ≫ (Spec.map (CommRingCat.ofHom
                  (algebraMap R' R''))) →
            x ≫ τ ≫ pullback.fst y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = v ≫
              ι.1) := by
  classical
  let k := IsLocalRing.ResidueField R
  let K := AlgebraicClosure k
  let φ₀ : R →+* K := (algebraMap k K).comp (IsLocalRing.residue R)
  have hφ₀m : ∀ x ∈ IsLocalRing.maximalIdeal R, φ₀ x = 0 := fun x hx => by
    change algebraMap k K (IsLocalRing.residue R x) = 0
    rw [(IsLocalRing.residue_eq_zero_iff x).mpr hx, map_zero]
  obtain ⟨x₀, hx₀⟩ := hYk
  obtain ⟨R₁, _, _, _, _, _, _, _, _, _, a₁, -, ha₁, -⟩ :=
    (open AlgebraicGeometry.Smooth in
      exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing
      y ⊤ x₀ hx₀ trivial)
  let : Algebra (base (K := K) hS hφ₀m).R' R₁ := ‹Algebra R R₁›
  have : Module.Finite (base (K := K) hS hφ₀m).R' R₁ := ‹Module.Finite R R₁›
  have : Algebra.Etale (base (K := K) hS hφ₀m).R' R₁ := ‹Algebra.Etale R R₁›
  have : Module.FaithfullyFlat (base (K := K) hS hφ₀m).R' R₁ := ‹Module.FaithfullyFlat R R₁›
  have : IsScalarTower R (base (K := K) hS hφ₀m).R' R₁ := IsScalarTower.of_algebraMap_eq (fun _
    => rfl)
  obtain ⟨E₁, hE₁sec, -, -⟩ := (base (K := K) hS hφ₀m).exists_next hS
    ((base (K := K) hS hφ₀m).t R₁ ≫ (base (K := K) hS hφ₀m).s) rfl a₁ (ha₁.trans (base (K := K)
      hS hφ₀m).s₂_eq)
  have : LocallyOfFiniteType (pullback.snd (pullback.fst y y ≫ y) (Spec.map (CommRingCat.ofHom
    φ₀))) :=
    MorphismProperty.of_isPullback
      (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback (pullback.fst y y ≫ y)
        (Spec.map (CommRingCat.ofHom φ₀))) inferInstance
  have : QuasiCompact (pullback.snd (pullback.fst y y ≫ y) (Spec.map (CommRingCat.ofHom φ₀))) :=
    MorphismProperty.of_isPullback
      (P := (@QuasiCompact : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback (pullback.fst y y ≫ y)
        (Spec.map (CommRingCat.ofHom φ₀))) inferInstance
  have : IsLocallyNoetherian (Level.Ω y φ₀) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (pullback.fst y y ≫ y) (Spec.map
      (CommRingCat.ofHom φ₀)))
  have : CompactSpace ↥(Level.Ω y φ₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (pullback.fst y y ≫ y) (Spec.map
      (CommRingCat.ofHom φ₀)))
  have : IsNoetherian (Level.Ω y φ₀) := {}
  obtain ⟨C, ⟨E, hEsec, rfl⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α :=
    TopologicalSpace.Closeds ↥(Level.Ω y φ₀)))
    {C | ∃ E : Level y U m K φ₀, E.HasSec ∧ (⟨E.Z hS, E.isClosed_Z hS⟩ :
      TopologicalSpace.Closeds ↥(Level.Ω y φ₀)) = C}
    ⟨_, E₁, hE₁sec, rfl⟩
  refine ⟨E.R', inferInstance, inferInstance, inferInstance, E.alg, E.fin, E.et, E.ff, E.Y',
    E.y', E.ι, E.U', E.m',
    E.sm, E.sep, inferInstance, E.qc, E.oi, E.hgen, E.hmax, E.hU'₁, E.hU'₂, E.hΦ', E.hΦ'₁,
      E.hΦ'₂, E.hΨ', E.hΨ'₁, E.hΨ'₂,
    E.hassoc', E.hext, hEsec, ?_⟩
  intro R'' _ _ _ _ _ _ _ a ha
  by_contra hn
  let : Algebra R R'' := ((algebraMap E.R' R'').comp (algebraMap R E.R')).toAlgebra
  have : IsScalarTower R E.R' R'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Module.Finite R R'' := Module.Finite.trans E.R' R''
  have : Algebra.Etale R R'' := Algebra.Etale.comp R E.R' R''
  have : Module.FaithfullyFlat R R'' := Module.FaithfullyFlat.trans R E.R' R''
  obtain ⟨b, hb⟩ := E.exists_not_mem_D hS (E.t R'' ≫ E.s) rfl a ha hn
  obtain ⟨E₂, hE₂sec, hsub, hne⟩ := E.exists_next hS (E.t R'' ≫ E.s) rfl a ha
  refine hmin ⟨E₂.Z hS, E₂.isClosed_Z hS⟩ ⟨E₂, hE₂sec, rfl⟩ (lt_of_le_of_ne hsub ?_)
  intro h
  exact hne b hb (congrArg (fun C : TopologicalSpace.Closeds ↥(Level.Ω y φ₀) => (C : Set
    ↥(Level.Ω y φ₀))) h)

end TranslationRefinement

end AbelianVarieties.NOSProofs.EtaleTranslationExtensions

namespace NeronModelInfra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian Topology
open AbelianVarieties.NOSProofs.EtaleTranslationExtensions

universe u

theorem exists_etale_translation_extension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback
        y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hU₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback
        y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback
        y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΦ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback
        y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback
        y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hΨ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback
        y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫
        pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y
        = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    (hYk : ∃ x : Y, y.base x = IsLocalRing.closedPoint R)
    (hUK : ∀ q : ↑(pullback y y), (pullback.fst y y ≫ y).base q ≠ IsLocalRing.closedPoint R → q
      ∈ U) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ :
      Algebra R R')
      (_ : Module.Finite R R') (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R')
      (Y' : Scheme.{u}) (y' : Y' ⟶ Spec (CommRingCat.of R'))
      (ι : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y')
      (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y'),
      Smooth y' ∧ IsSeparated y' ∧ LocallyOfFiniteType y' ∧ QuasiCompact y' ∧
      IsOpenImmersion ι.1 ∧
      (∀ p : Y', y'.base p ≠ IsLocalRing.closedPoint R' → p ∈ Set.range ι.1.base) ∧
      (∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y')))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y')))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
          (u v p q : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y')),
        u.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.fst y' y' →
        p.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 →
        p.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.snd y' y' →
        q.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U'.ι ≫ pullback.fst y' y' →
        q.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ m'.1 →
        p.1 ≫ m'.1 = q.1 ≫ m'.1) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
          (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫
            pullback.fst y y ≫ y))
          (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y),
        a.1 = w.1 ≫ U.ι ≫ pullback.fst y y → b.1 = w.1 ≫ U.ι ≫ pullback.snd y y → c.1 = w.1 ≫ m.1 →
        ∃ w' : SchemeHomOver t' (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map
            (CommRingCat.ofHom (algebraMap R R'))) a).1 ≫ ι.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map
            (CommRingCat.ofHom (algebraMap R R'))) b).1 ≫ ι.1 ∧
          w'.1 ≫ m'.1 = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom
            (algebraMap R R'))) c).1 ≫ ι.1) ∧
      (∃ a' : Spec (CommRingCat.of R') ⟶ Y', a' ≫ y' = 𝟙 _) ∧
      (∀ (R'' : Type u) (_ : CommRing R'') (_ : IsDomain R'') (_ : IsDiscreteValuationRing R'')
          (_ : Algebra R' R'') (_ : Module.Finite R' R'') (_ : Algebra.Etale R' R'') (_ :
            Module.FaithfullyFlat R' R'')
          (a : Spec (CommRingCat.of R'') ⟶ Y),
        a ≫ y = (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map
          (CommRingCat.ofHom (algebraMap R R'))) →
        ∃ τ : pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map
          (CommRingCat.ofHom (algebraMap R R')))) ⟶ pullback y' (Spec.map (CommRingCat.ofHom
            (algebraMap R' R''))),
          τ ≫ pullback.snd y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = pullback.snd
            y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom
              (algebraMap R R')))) ∧
          ∀ {T : Scheme.{u}} (x : T ⟶ pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R'
            R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))))
            (w : T ⟶ (U : Scheme.{u})) (v : T ⟶ pullback y (Spec.map (CommRingCat.ofHom
              (algebraMap R R')))),
            w ≫ U.ι ≫ pullback.fst y y = x ≫ pullback.snd y ((Spec.map (CommRingCat.ofHom
              (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ a →
            w ≫ U.ι ≫ pullback.snd y y = x ≫ pullback.fst y ((Spec.map (CommRingCat.ofHom
              (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) →
            v ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ m.1 →
            v ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = x ≫
              pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map
                (CommRingCat.ofHom (algebraMap R R')))) ≫ (Spec.map (CommRingCat.ofHom
                  (algebraMap R' R''))) →
            x ≫ τ ≫ pullback.fst y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = v ≫
              ι.1) :=
  TranslationRefinement.main y U m ⟨hU₁, hU₂, hΦ, hΦ₁, hΦ₂, hΨ, hΨ₁, hΨ₂, hassoc, hUK⟩ hYk

end NeronModelInfra

namespace AbelianVarieties.NOSProofs.EtaleTranslationExtensions
end AbelianVarieties.NOSProofs.EtaleTranslationExtensions
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_etale_translation_cover.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.EtaleTranslationCovers


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace MaximalSpecializations

theorem exists_maximal_specializes {X : Scheme.{u}} (S : Set X) (hS : IsClosed S) (x : X) (hx :
  x ∈ S) :
    ∃ η ∈ S, η ⤳ x ∧ ∀ y ∈ S, y ⤳ η → y = η := by
  have : QuasiSober S := hS.isClosedEmbedding_subtypeVal.quasiSober
  set Z : Set S := irreducibleComponent (⟨x, hx⟩ : S) with hZ
  have hZirr : IsIrreducible Z := isIrreducible_irreducibleComponent
  have hZcl : IsClosed Z :=
    isClosed_of_mem_irreducibleComponents _ (irreducibleComponent_mem_irreducibleComponents _)
  obtain ⟨η, hη⟩ := QuasiSober.sober hZirr hZcl
  refine ⟨η.1, η.2, ?_, ?_⟩
  · have h1 : η ⤳ (⟨x, hx⟩ : S) := hη.specializes mem_irreducibleComponent
    exact h1.map continuous_subtype_val
  · intro y hyS hyη
    have h1 : (⟨y, hyS⟩ : S) ⤳ η := by
      rwa [← Topology.IsInducing.subtypeVal.specializes_iff]
    have h2 : Z ⊆ closure {(⟨y, hyS⟩ : S)} := by
      rw [← hη.def]
      exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 h1))
        isClosed_closure
    have h3 : closure {(⟨y, hyS⟩ : S)} = Z :=
      eq_irreducibleComponent isIrreducible_singleton.closure.isPreirreducible h2
    have h4 : IsGenericPoint (⟨y, hyS⟩ : S) Z := h3
    exact congrArg Subtype.val (h4.eq hη)

end MaximalSpecializations

end AbelianVarieties.NOSProofs.EtaleTranslationCovers

namespace NeronModelInfra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian Topology
open AbelianVarieties.NOSProofs.EtaleTranslationCovers
open AbelianVarieties.NOSProofs.EtaleTranslationCovers.MaximalSpecializations

open NeronModelInfra renaming
 exists_forall_dense_preimage_fibre_comp_eq_comp_of_forall_dense_preimage_fibre_of_relativeGroupLaw
 → restrictMultiplication

universe u

theorem exists_etale_translation_cover
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hXk : ∃ x : X, f.base x = IsLocalRing.closedPoint R)
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (_hW₁ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R → p
      ∈ W)
    (_hW₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R
        → y = p) →
      p ∈ W)
    (hmK : (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f)
              ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (hΦ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)))
    (_hΦ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R
        → y = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)).base)
    (hΨ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (_hΨ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R
        → y = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)
    (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
    (_hX'₁ : ∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X')
    (hX'₂ : ∀ x : X, f.base x = IsLocalRing.closedPoint R →
      (∀ y : X, y ⤳ x → f.base y = IsLocalRing.closedPoint R → y = x) → x ∈ X')
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q
      ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd
      f f).base q ∈ X' ∧
      m.1.base ⟨q, hUW hq⟩ ∈ X')
    (hU₃ : ∀ x : X, x ∈ X' →
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} →
          ↑(pullback f f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} →
          ↑(pullback f f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} →
          ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} →
          ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} →
          ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈
              U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} →
          ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈
              U}))) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ :
      Algebra R R')
      (_ : Module.Finite R R') (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R')
      (Y' : Scheme.{u}) (y' : Y' ⟶ Spec (CommRingCat.of R'))
      (ι : SchemeHomOver (pullback.snd (X'.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R
        R')))) y')
      (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y'),
      Smooth y' ∧ IsSeparated y' ∧ LocallyOfFiniteType y' ∧ QuasiCompact y' ∧
      IsOpenImmersion ι.1 ∧
      (∀ p : Y', y'.base p ≠ IsLocalRing.closedPoint R' → p ∈ Set.range ι.1.base) ∧
      (∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y')))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y')))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
          (u v p q : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y')),
        u.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.fst y' y' →
        p.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 →
        p.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.snd y' y' →
        q.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U'.ι ≫ pullback.fst y' y' →
        q.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ m'.1 →
        p.1 ≫ m'.1 = q.1 ≫ m'.1) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
          (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫
            pullback.fst f f ≫ f))
          (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (X'.ι ≫
            f)),
        a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
        c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
        ∃ w' : SchemeHomOver t' (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map
            (CommRingCat.ofHom (algebraMap R R'))) a).1 ≫ ι.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map
            (CommRingCat.ofHom (algebraMap R R'))) b).1 ≫ ι.1 ∧
          w'.1 ≫ m'.1 = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom
            (algebraMap R R'))) c).1 ≫ ι.1) ∧
      (∃ a' : Spec (CommRingCat.of R') ⟶ Y', a' ≫ y' = 𝟙 _) ∧
      (∀ q : ↑(pullback y' y'), (pullback.fst y' y').base q ∈ Set.range ι.1.base →
        (pullback.snd y' y').base q ∈ Set.range ι.1.base → q ∈ U') := by
  classical
  obtain ⟨UY, mY, hY₁, hY₂, hYΦ, hYΦ₁, hYΦ₂, hYΨ, hYΨ₁, hYΨ₂, hassocY, hgenY, hrel⟩ :=
    restrictMultiplication
      K LXK f e W m hmK hΦ hΨ X' U hUW hU₁ hU₂ hU₃
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  have : CompactSpace ↥(X' : Scheme.{u}) :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (X' : Set X))
  have : IsNoetherian (X' : Scheme.{u}) := {}
  have : QuasiCompact (X'.ι ≫ f) := inferInstance
  have : Smooth (X'.ι ≫ f) := inferInstance
  have : IsSeparated (X'.ι ≫ f) := inferInstance
  have : LocallyOfFiniteType (X'.ι ≫ f) := inferInstance
  have hYk : ∃ x : ↥(X' : Scheme.{u}), (X'.ι ≫ f).base x = IsLocalRing.closedPoint R := by
    obtain ⟨x₀, hx₀⟩ := hXk
    have hS : IsClosed {x : X | f.base x = IsLocalRing.closedPoint R} := by
      have : IsClosed ({IsLocalRing.closedPoint R} : Set (Spec (CommRingCat.of R))) :=
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 (IsLocalRing.maximalIdeal.isMaximal R)
      exact this.preimage f.base.hom.continuous
    obtain ⟨η, hηS, -, hηmax⟩ := exists_maximal_specializes {x : X | f.base x =
      IsLocalRing.closedPoint R} hS x₀ hx₀
    have hηX' : η ∈ X' := hX'₂ η hηS (fun y hy hyk => hηmax y hyk hy)
    exact ⟨⟨η, hηX'⟩, hηS⟩
  obtain ⟨R', instCR, instDom, instDVR, instAlg, instFin, instEt, instFF, Y', y', ι, U', m',
      hsm, hsep, hloft, hqc, hιo, hgen, hmax, hU'₁, hU'₂, hΦ', hΦ'₁, hΦ'₂, hΨ', hΨ'₁, hΨ'₂,
        hassoc',
      hext, hsec, hstat⟩ :=
    NeronModelInfra.exists_etale_translation_extension
      (X'.ι ≫ f) UY mY hY₁ hY₂ hYΦ hYΦ₁ hYΦ₂ hYΨ hYΨ₁ hYΨ₂ (fun t u v p q => hassocY t u v p q)
        hYk hgenY
  have : Smooth y' := hsm
  have : IsSeparated y' := hsep
  have : LocallyOfFiniteType y' := hloft
  have : QuasiCompact y' := hqc
  have : IsOpenImmersion ι.1 := hιo
  obtain ⟨U'', hle, m'', hm''m', hU''₁, hU''₂, hΦ'', hΦ''₁, hΦ''₂, hΨ'', hΨ''₁, hΨ''₂, hassoc'',
    hsq⟩ :=
    exists_opens_forall_mem_of_mem_range_of_forall_exists_translation_of_henselianLocalRing
      (X'.ι ≫ f) UY mY hY₁ hY₂ hYΦ hYΦ₁ hYΦ₂ hYΨ hYΨ₁ hYΨ₂ (fun t u v p q => hassocY t u v p q)
        hgenY
      R' y' ι U' m' hU'₁ hU'₂ hΦ' hΦ'₁ hΦ'₂ hΨ' hΨ'₁ hΨ'₂ (fun t u v p q => hassoc' t u v p q)
      (fun t' w a b c ha hb hc => hext t' w a b c ha hb hc) hstat
  refine ⟨R', instCR, instDom, instDVR, instAlg, instFin, instEt, instFF, Y', y', ι, U'', m'',
    hsm, hsep, hloft, hqc, hιo, hgen, hmax, hU''₁, hU''₂, hΦ'', hΦ''₁, hΦ''₂, hΨ'', hΨ''₁, hΨ''₂,
    (fun t u v p q => hassoc'' t u v p q), ?_, hsec, hsq⟩
  intro T t' w a b c ha hb hc
  obtain ⟨v, hv₁, hv₂, hv₃⟩ := hrel w.1 a.1 b.1 ha hb
  have hcv : c.1 = v ≫ mY.1 := by
    rw [← cancel_mono X'.ι, Category.assoc, hv₃, hc]
  let wY : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f)) :=
    ⟨v, by
      have h := a.2
      rw [← hv₁] at h
      simpa only [Category.assoc] using h⟩
  obtain ⟨w', e₁, e₂, e₃⟩ := hext t' wY a b c hv₁.symm hv₂.symm hcv
  refine ⟨⟨w'.1 ≫ (pullback y' y').homOfLE hle, ?_⟩, ?_, ?_, ?_⟩
  · rw [Category.assoc, Scheme.homOfLE_ι_assoc]; exact w'.2
  · change (w'.1 ≫ (pullback y' y').homOfLE hle) ≫ U''.ι ≫ pullback.fst y' y' = _
    rw [Category.assoc, Scheme.homOfLE_ι_assoc]; exact e₁
  · change (w'.1 ≫ (pullback y' y').homOfLE hle) ≫ U''.ι ≫ pullback.snd y' y' = _
    rw [Category.assoc, Scheme.homOfLE_ι_assoc]; exact e₂
  · change (w'.1 ≫ (pullback y' y').homOfLE hle) ≫ m''.1 = _
    rw [Category.assoc, hm''m']; exact e₃

end NeronModelInfra

namespace AbelianVarieties.NOSProofs.EtaleTranslationCovers
end AbelianVarieties.NOSProofs.EtaleTranslationCovers
end
