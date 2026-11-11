/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.EffectiveEpi
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Choose
public import Nyll.AbelianVarieties.Geometry.GroupLaw
public import Nyll.AbelianVarieties.Geometry.Quotients.Action
public import Nyll.AbelianVarieties.Geometry.Quotients.FiniteSlices
public import Nyll.AbelianVarieties.Geometry.Quotients.Slices
public import Nyll.AbelianVarieties.Geometry.RelativeDimension
public import Nyll.AbelianVarieties.NeronModels.Endomorphisms
public import Nyll.SchemeTheory.Descent.FlatMorphisms
public import Nyll.SchemeTheory.Descent.FiniteQuotients
public import Nyll.AbelianVarieties.Basic
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Action
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Kernel
public import Nyll.AlgebraicCurves.Geometry.Schemes.Quotients.QuotientFiniteLocallyFreeEquivalenceRelation
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Descent of quotient group schemes

Descend the relative group law through a flat quotient and glue quotient charts
constructed from transverse étale slices. The quotient retains the expected
relative dimension and kernel.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isPullback_action_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.QuotientGroupLaw

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

namespace Laws
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian

section Points

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L :
    RelativeGroupLaw R f)

variable {E : Scheme.{u}} (ι : E ⟶ J)

theorem comp_action {T : Scheme.{u}} (φ : T ⟶ pullback (ι ≫ f) f) :
    φ ≫ L.action ι = (L.mul (φ ≫ RelativeGroupLaw.actionSource f ι)
      (GoodReductionJacobian.schemeHomOverComp φ rfl (L.actionFstPoint ι))
      (GoodReductionJacobian.schemeHomOverComp φ rfl (L.actionSndPoint ι))).1 := by
  rw [← L.mul_natural _ _ φ rfl, GoodReductionJacobian.schemeHomOverComp_coe,
    RelativeGroupLaw.action_def]

theorem comp_action' {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (φ : T ⟶ pullback (ι ≫ f) f)
    (ht : φ ≫ RelativeGroupLaw.actionSource f ι = t) :
    φ ≫ L.action ι = (L.mul t ⟨φ ≫ pullback.fst _ _ ≫ ι, by
        rw [← ht, Category.assoc, Category.assoc]; exact congrArg (φ ≫ ·) pullback.condition⟩
      ⟨φ ≫ pullback.snd _ _, by rw [← ht, Category.assoc]⟩).1 := by
  subst ht
  rw [comp_action]
  congr 1

/-- A pair of compatible relative points in the action pullback. -/
noncomputable def pt {T : Scheme.{u}} (e : T ⟶ E) (x : T ⟶ J) (h : e ≫ ι ≫ f = x ≫ f) : T ⟶ pullback
    (ι ≫ f) f :=
  pullback.lift e x h

@[scoped simp] theorem pt_fst {T : Scheme.{u}} (e : T ⟶ E) (x : T ⟶ J) (h : e ≫ ι ≫ f = x ≫ f) : pt
    ι e x h ≫ pullback.fst _ _ = e :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem pt_snd {T : Scheme.{u}} (e : T ⟶ E) (x : T ⟶ J) (h : e ≫ ι ≫ f = x ≫ f) : pt
    ι e x h ≫ pullback.snd _ _ = x :=
  pullback.lift_snd _ _ _

theorem comp_action_pt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (e : T ⟶ E) (x :
    SchemeHomOver t f)
    (he : e ≫ ι ≫ f = t) (hx : e ≫ ι ≫ f = x.1 ≫ f) :
    pt ι e x.1 hx ≫ L.action ι = (L.mul t ⟨e ≫ ι, he⟩ x).1 := by
  have hsrc : pt ι e x.1 hx ≫ RelativeGroupLaw.actionSource f ι = t := by
    change pt ι e x.1 hx ≫ (pullback.snd _ _ ≫ f) = t
    rw [← Category.assoc, pt_snd]; exact x.2
  rw [comp_action' L ι t _ hsrc]
  congr 2
  · exact Subtype.ext (by change pt ι e x.1 hx ≫ pullback.fst _ _ ≫ ι = e ≫ ι; rw [← Category.assoc,
      pt_fst])
  · exact Subtype.ext (by change pt ι e x.1 hx ≫ pullback.snd _ _ = x.1; rw [pt_snd])

variable {P : Scheme.{u}} (p : J ⟶ P) (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p)

include w in
theorem p_act {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (e : T ⟶ E) (z : SchemeHomOver t f)
    (he : e ≫ ι ≫ f = t) :
    (L.mul t ⟨e ≫ ι, he⟩ z).1 ≫ p = z.1 ≫ p := by
  have hx : e ≫ ι ≫ f = z.1 ≫ f := by rw [he, z.2]
  rw [← comp_action_pt L ι t e z he hx, Category.assoc, ← w, ← Category.assoc, pt_snd]

theorem exists_eq_mul_of_comp_eq (hR : IsPullback (pullback.snd (ι ≫ f) f) (L.action ι) p p)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (y₁ y₂ : SchemeHomOver t f) (h : y₁.1 ≫ p =
      y₂.1 ≫ p) :
    ∃ (e : T ⟶ E) (he : e ≫ ι ≫ f = t), y₂ = L.mul t ⟨e ≫ ι, he⟩ y₁ := by
  let φ := hR.lift y₁.1 y₂.1 h
  have hφ₁ : φ ≫ pullback.snd (ι ≫ f) f = y₁.1 := hR.lift_fst _ _ _
  have hφ₂ : φ ≫ L.action ι = y₂.1 := hR.lift_snd _ _ _
  have ht : φ ≫ RelativeGroupLaw.actionSource f ι = t := by
    change φ ≫ (pullback.snd _ _ ≫ f) = t
    rw [← Category.assoc, hφ₁]; exact y₁.2
  have he : (φ ≫ pullback.fst (ι ≫ f) f) ≫ ι ≫ f = t := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hφ₁]
    exact y₁.2
  refine ⟨φ ≫ pullback.fst _ _, he, ?_⟩
  apply Subtype.ext
  rw [← hφ₂, comp_action' L ι t φ ht]
  congr 2
  all_goals exact Subtype.ext hφ₁

end Points

section Maps

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L :
    RelativeGroupLaw R f)

/-- Multiplication as a scheme morphism. -/
noncomputable def mJ : pullback f f ⟶ J :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f,
    pullback.condition.symm⟩).1

theorem mJ_over : mJ L ≫ f = pullback.fst f f ≫ f := (L.mul _ _ _).2

theorem comp_mJ₀ {T : Scheme.{u}} (ψ : T ⟶ pullback f f) :
    ψ ≫ mJ L = (L.mul (ψ ≫ pullback.fst f f ≫ f)
      (GoodReductionJacobian.schemeHomOverComp ψ rfl (⟨pullback.fst f f, rfl⟩ : SchemeHomOver
        (pullback.fst f f ≫ f) f))
      (GoodReductionJacobian.schemeHomOverComp ψ rfl (⟨pullback.snd f f, pullback.condition.symm⟩ :
        SchemeHomOver (pullback.fst f f ≫ f) f))).1 := by
  rw [← L.mul_natural _ _ ψ rfl, GoodReductionJacobian.schemeHomOverComp_coe]; rfl

theorem comp_mJ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (ψ : T ⟶ pullback f f) (ht : ψ ≫
    pullback.fst f f ≫ f = t) :
    ψ ≫ mJ L = (L.mul t ⟨ψ ≫ pullback.fst f f, ht⟩ ⟨ψ ≫ pullback.snd f f, by rw [← ht,
      Category.assoc, pullback.condition]⟩).1 := by
  subst ht
  rw [comp_mJ₀]
  rfl

/-- Inversion as a scheme morphism. -/
noncomputable def iJ : J ⟶ J := (L.inv f ⟨𝟙 J, Category.id_comp f⟩).1

theorem iJ_over : iJ L ≫ f = f := (L.inv f _).2

theorem comp_iJ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) : x.1 ≫
    iJ L = (L.inv t x).1 := by
  obtain ⟨x, rfl⟩ := x
  have h := congrArg Subtype.val (L.inv_natural f (x ≫ f) x rfl ⟨𝟙 J, Category.id_comp f⟩)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  rw [iJ, h]
  have hx : GoodReductionJacobian.schemeHomOverComp x rfl (⟨𝟙 J, Category.id_comp f⟩ : SchemeHomOver
    f f) =
      (⟨x, rfl⟩ : SchemeHomOver (x ≫ f) f) := Subtype.ext (Category.comp_id x)
  rw [hx]

/-- The unit section. -/
noncomputable def eJ : Spec (CommRingCat.of R) ⟶ J := (L.one (𝟙 _)).1

theorem eJ_over : eJ L ≫ f = 𝟙 _ := (L.one _).2

theorem comp_eJ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : t ≫ eJ L = (L.one t).1 := by
  have h := congrArg Subtype.val (L.one_natural (𝟙 _) t t (Category.comp_id t))
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  rw [eJ, h]

end Maps

section Products

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}
  {P : Scheme.{u}} (g : P ⟶ Spec (CommRingCat.of R)) (p : J ⟶ P) (hg : p ≫ g = f)

/-- The first stage of the quotient product map. -/
noncomputable def oneP : pullback f f ⟶ pullback f g :=
  pullback.map f f f g (𝟙 J) p (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw
    [Category.comp_id, hg])

@[reassoc (attr := simp)] theorem oneP_fst : oneP g p hg ≫ pullback.fst _ _ = pullback.fst f f := by
  rw [oneP, pullback.lift_fst, Category.comp_id]
@[reassoc (attr := simp)] theorem oneP_snd : oneP g p hg ≫ pullback.snd _ _ = pullback.snd f f ≫ p
    := pullback.lift_snd _ _ _

theorem isPullback_oneP : IsPullback (pullback.snd f f) (oneP g p hg) p (pullback.snd f g) := by
  have outer : IsPullback (oneP g p hg ≫ pullback.fst f g) (pullback.snd f f) f (p ≫ g) := by
    rw [oneP_fst, hg]; exact IsPullback.of_hasPullback f f
  exact (IsPullback.of_right outer (oneP_snd g p hg) (IsPullback.of_hasPullback f g)).flip

/-- The second stage of the quotient product map. -/
noncomputable def twoP : pullback f g ⟶ pullback g g :=
  pullback.map f g g g p (𝟙 P) (𝟙 _) (by rw [Category.comp_id, hg]) (by rw [Category.comp_id,
    Category.id_comp])

@[reassoc (attr := simp)] theorem twoP_fst : twoP g p hg ≫ pullback.fst _ _ = pullback.fst f g ≫ p
    := pullback.lift_fst _ _ _
@[reassoc (attr := simp)] theorem twoP_snd : twoP g p hg ≫ pullback.snd _ _ = pullback.snd f g := by
  rw [twoP, pullback.lift_snd, Category.comp_id]

theorem isPullback_twoP : IsPullback (pullback.fst f g) (twoP g p hg) p (pullback.fst g g) := by
  have outer : IsPullback (twoP g p hg ≫ pullback.snd g g) (pullback.fst f g) g (p ≫ g) := by
    rw [twoP_snd, hg]; exact (IsPullback.of_hasPullback f g).flip
  exact (IsPullback.of_right outer (twoP_fst g p hg) (IsPullback.of_hasPullback g g).flip).flip

variable [Flat p] [Surjective p] [QuasiCompact p]

scoped instance flat_oneP : Flat (oneP g p hg) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_oneP g p hg) inferInstance
scoped instance surjective_oneP : Surjective (oneP g p hg) :=
  MorphismProperty.of_isPullback (P := @Surjective) (isPullback_oneP g p hg) inferInstance
scoped instance quasiCompact_oneP : QuasiCompact (oneP g p hg) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_oneP g p hg) inferInstance
scoped instance flat_twoP : Flat (twoP g p hg) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_twoP g p hg) inferInstance
scoped instance surjective_twoP : Surjective (twoP g p hg) :=
  MorphismProperty.of_isPullback (P := @Surjective) (isPullback_twoP g p hg) inferInstance
scoped instance quasiCompact_twoP : QuasiCompact (twoP g p hg) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_twoP g p hg) inferInstance

omit [QuasiCompact p] in
theorem epi_p : Epi p := Flat.epi_of_flat_of_surjective p

omit [QuasiCompact p] in
theorem epi_pp : Epi (oneP g p hg ≫ twoP g p hg) := by
  have : Epi (oneP g p hg) := Flat.epi_of_flat_of_surjective (oneP g p hg)
  have : Epi (twoP g p hg) := Flat.epi_of_flat_of_surjective (twoP g p hg)
  exact epi_comp _ _

omit [Flat p] [Surjective p] [QuasiCompact p] in
theorem pp_fst : (oneP g p hg ≫ twoP g p hg) ≫ pullback.fst _ _ = pullback.fst f f ≫ p := by
  rw [Category.assoc, twoP_fst, oneP_fst_assoc]

omit [Flat p] [Surjective p] [QuasiCompact p] in
theorem pp_snd : (oneP g p hg ≫ twoP g p hg) ≫ pullback.snd _ _ = pullback.snd f f ≫ p := by
  rw [Category.assoc, twoP_snd, oneP_snd]

end Products

section Descent

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L :
    RelativeGroupLaw R f)
  {E : Scheme.{u}} (ι : E ⟶ J)
  {P : Scheme.{u}} (g : P ⟶ Spec (CommRingCat.of R)) (p : J ⟶ P) (hg : p ≫ g = f)
  (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p)
  [Flat p] [Surjective p] [QuasiCompact p]
  (hR : IsPullback (pullback.snd (ι ≫ f) f) (L.action ι) p p)
  (hE_inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (e : T ⟶ E) (he : e ≫ ι ≫ f = t),
    ∃ e' : T ⟶ E, e' ≫ ι = (L.inv t ⟨e ≫ ι, he⟩).1)
  (hE_norm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (e : T ⟶
    E)
    (he : e ≫ ι ≫ f = t), ∃ e' : T ⟶ E, e' ≫ ι = (L.mul t (L.mul t x ⟨e ≫ ι, he⟩) (L.inv t x)).1)

include hg w hR hE_inv hE_norm

omit hg w [Flat p] [Surjective p] [QuasiCompact p] hR hE_inv in
theorem exists_mul_act_eq {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a y : SchemeHomOver t
    f) (e : T ⟶ E)
    (he : e ≫ ι ≫ f = t) :
    ∃ (e' : T ⟶ E) (he' : e' ≫ ι ≫ f = t), L.mul t a (L.mul t ⟨e ≫ ι, he⟩ y) = L.mul t ⟨e' ≫ ι, he'⟩
      (L.mul t a y) := by
  obtain ⟨e', he'⟩ := hE_norm t a e he
  have he'f : e' ≫ ι ≫ f = t := by rw [← Category.assoc, he']; exact (L.mul t _ _).2
  refine ⟨e', he'f, ?_⟩
  have hpt : (⟨e' ≫ ι, he'f⟩ : SchemeHomOver t f) = L.mul t (L.mul t a ⟨e ≫ ι, he⟩) (L.inv t a) :=
    Subtype.ext he'
  rw [hpt]
  let : Group (SchemeHomOver t f) := L.pointGroup t
  change a * (⟨e ≫ ι, he⟩ * y) = (a * ⟨e ≫ ι, he⟩ * a⁻¹) * (a * y)
  group

omit [Flat p] [Surjective p] [QuasiCompact p] hE_inv in
theorem cond_one {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ pullback f f) (h : g₁ ≫ oneP g p hg = g₂ ≫ oneP g p
    hg) :
    g₁ ≫ (mJ L ≫ p) = g₂ ≫ (mJ L ≫ p) := by
  have ha : g₁ ≫ pullback.fst f f = g₂ ≫ pullback.fst f f := by
    rw [← oneP_fst g p hg, ← Category.assoc, h, Category.assoc]
  have hy : (g₁ ≫ pullback.snd f f) ≫ p = (g₂ ≫ pullback.snd f f) ≫ p := by
    rw [Category.assoc, Category.assoc, ← oneP_snd g p hg, ← Category.assoc, h, Category.assoc]
  let t : Z ⟶ Spec (CommRingCat.of R) := g₁ ≫ pullback.fst f f ≫ f
  have ht₂ : g₂ ≫ pullback.fst f f ≫ f = t := by rw [← Category.assoc, ← ha, Category.assoc]
  rw [← Category.assoc, ← Category.assoc, comp_mJ L t g₁ rfl, comp_mJ L t g₂ ht₂]
  obtain ⟨e, he, hey⟩ := exists_eq_mul_of_comp_eq L ι p hR t
    ⟨g₁ ≫ pullback.snd f f, by rw [Category.assoc, ← pullback.condition]⟩
    ⟨g₂ ≫ pullback.snd f f, by rw [← ht₂, Category.assoc, ← pullback.condition]⟩ hy
  have hX : (⟨g₂ ≫ pullback.fst f f, ht₂⟩ : SchemeHomOver t f) = ⟨g₁ ≫ pullback.fst f f, rfl⟩ :=
    Subtype.ext ha.symm
  rw [hX, hey]
  obtain ⟨e', he', hmul⟩ := exists_mul_act_eq L ι hE_norm t ⟨g₁ ≫ pullback.fst f
    f, rfl⟩
    ⟨g₁ ≫ pullback.snd f f, by rw [Category.assoc, ← pullback.condition]⟩ e he
  rw [hmul, p_act L ι p w t e' _ he']

omit hE_inv in
/-- Multiplication descended in the second argument. -/
noncomputable def mOne : pullback f g ⟶ P :=
  EffectiveEpi.desc (oneP g p hg) (mJ L ≫ p) (cond_one L ι g p hg w hR hE_norm)

omit hE_inv in
theorem oneP_mOne : oneP g p hg ≫ mOne L ι g p hg w hR hE_norm = mJ L ≫ p :=
  EffectiveEpi.fac (oneP g p hg) (mJ L ≫ p) (cond_one L ι g p hg w hR hE_norm)

omit hE_inv in
theorem cond_two {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ pullback f g) (h : g₁ ≫ twoP g p hg = g₂ ≫ twoP g p
    hg) :
    g₁ ≫ mOne L ι g p hg w hR hE_norm = g₂ ≫ mOne L ι g p hg w hR hE_norm := by
  have hv : g₁ ≫ pullback.snd f g = g₂ ≫ pullback.snd f g := by
    rw [← twoP_snd g p hg, ← Category.assoc, h, Category.assoc]
  have hx : (g₁ ≫ pullback.fst f g) ≫ p = (g₂ ≫ pullback.fst f g) ≫ p := by
    rw [Category.assoc, Category.assoc, ← twoP_fst g p hg, ← Category.assoc, h, Category.assoc]
  let c := pullback.fst g₁ (oneP g p hg)
  let d₁ := pullback.snd g₁ (oneP g p hg)
  have hcd : c ≫ g₁ = d₁ ≫ oneP g p hg := pullback.condition
  have : Flat c :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@Flat : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback g₁ (oneP g p hg)).flip inferInstance
  have : Surjective c :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@Surjective : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback g₁ (oneP g p hg)).flip inferInstance
  have : Epi c := Flat.epi_of_flat_of_surjective c
  rw [← cancel_epi c, ← Category.assoc, ← Category.assoc, hcd, Category.assoc, oneP_mOne]
  have e1 : c ≫ g₂ ≫ pullback.snd f g ≫ g = d₁ ≫ pullback.snd f f ≫ f :=
    calc c ≫ g₂ ≫ pullback.snd f g ≫ g = c ≫ g₁ ≫ pullback.snd f g ≫ g := by
          rw [← Category.assoc g₂, ← hv, Category.assoc]
      _ = d₁ ≫ oneP g p hg ≫ pullback.snd f g ≫ g := by rw [← Category.assoc, hcd, Category.assoc]
      _ = d₁ ≫ pullback.snd f f ≫ p ≫ g := by rw [oneP_snd_assoc]
      _ = d₁ ≫ pullback.snd f f ≫ f := by rw [hg]
  have hd₂ : (c ≫ g₂ ≫ pullback.fst f g) ≫ f = (d₁ ≫ pullback.snd f f) ≫ f := by
    simp only [Category.assoc]
    rw [pullback.condition]
    exact e1
  let d₂ : _ ⟶ pullback f f := pullback.lift (c ≫ g₂ ≫ pullback.fst f g) (d₁ ≫ pullback.snd f f) hd₂
  have hd₂P : d₂ ≫ oneP g p hg = c ≫ g₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, oneP_fst, pullback.lift_fst, Category.assoc]
    · rw [Category.assoc, oneP_snd, pullback.lift_snd_assoc, Category.assoc, Category.assoc, ← hv,
        ← Category.assoc c g₁, hcd, Category.assoc, oneP_snd]
  rw [← hd₂P, Category.assoc, oneP_mOne]
  let t := d₁ ≫ pullback.fst f f ≫ f
  have ht₂ : d₂ ≫ pullback.fst f f ≫ f = t := by
    change d₂ ≫ pullback.fst f f ≫ f = d₁ ≫ pullback.fst f f ≫ f
    rw [pullback.condition, ← Category.assoc, pullback.lift_snd, Category.assoc]
  rw [← Category.assoc, ← Category.assoc d₂, comp_mJ L t d₁ rfl, comp_mJ L t d₂ ht₂]
  have hx' : (d₁ ≫ pullback.fst f f) ≫ p = (d₂ ≫ pullback.fst f f) ≫ p := by
    have e1 : d₁ ≫ pullback.fst f f = c ≫ g₁ ≫ pullback.fst f g := by
      rw [← oneP_fst g p hg, ← Category.assoc, ← hcd, Category.assoc]
    have e2 : d₂ ≫ pullback.fst f f = c ≫ g₂ ≫ pullback.fst f g := pullback.lift_fst _ _ _
    have hx2 : g₁ ≫ pullback.fst f g ≫ p = g₂ ≫ pullback.fst f g ≫ p := by simpa only
      [Category.assoc] using hx
    rw [e1, e2]
    simp only [Category.assoc]
    rw [hx2]
  obtain ⟨e, he, hey⟩ := exists_eq_mul_of_comp_eq L ι p hR t ⟨d₁ ≫ pullback.fst f f, rfl⟩ ⟨d₂ ≫
    pullback.fst f f, ht₂⟩ hx'
  have hY : (⟨d₂ ≫ pullback.snd f f, by rw [← ht₂, Category.assoc, pullback.condition]⟩ :
    SchemeHomOver t f) =
      ⟨d₁ ≫ pullback.snd f f, by rw [Category.assoc, ← pullback.condition]⟩ := Subtype.ext
        (pullback.lift_snd _ _ _)
  rw [hY, hey, L.mul_assoc, p_act L ι p w t e _ he]

omit hE_inv in
/-- The descended multiplication morphism. -/
noncomputable def mP : pullback g g ⟶ P :=
  EffectiveEpi.desc (twoP g p hg) (mOne L ι g p hg w hR hE_norm) (cond_two L ι g p hg w hR hE_norm)

omit hE_inv in
theorem twoP_mP : twoP g p hg ≫ mP L ι g p hg w hR hE_norm = mOne L ι g p hg w hR hE_norm :=
  EffectiveEpi.fac (twoP g p hg) (mOne L ι g p hg w hR hE_norm) (cond_two L ι g p hg w hR hE_norm)

omit hE_inv in
theorem pp_mP : (oneP g p hg ≫ twoP g p hg) ≫ mP L ι g p hg w hR hE_norm = mJ L ≫ p := by
  rw [Category.assoc, twoP_mP, oneP_mOne]

omit hE_inv in
theorem mP_over : mP L ι g p hg w hR hE_norm ≫ g = pullback.fst _ _ ≫ g := by
  have : Epi (oneP g p hg ≫ twoP g p hg) := epi_pp g p hg
  rw [← cancel_epi (oneP g p hg ≫ twoP g p hg), ← Category.assoc, pp_mP, Category.assoc, hg,
    mJ_over,
    ← Category.assoc, pp_fst, Category.assoc, hg]

omit [Flat p] [Surjective p] [QuasiCompact p] in
theorem cond_inv {Z : Scheme.{u}} (y₁ y₂ : Z ⟶ J) (h : y₁ ≫ p = y₂ ≫ p) : y₁ ≫ (iJ L ≫ p) = y₂ ≫ (iJ
    L ≫ p) := by
  let t : Z ⟶ Spec (CommRingCat.of R) := y₁ ≫ f
  have ht₂ : y₂ ≫ f = t := by
    change y₂ ≫ f = y₁ ≫ f
    rw [← hg, ← Category.assoc, ← h, Category.assoc]
  rw [← Category.assoc, ← Category.assoc, comp_iJ L t ⟨y₁, rfl⟩, comp_iJ L t ⟨y₂, ht₂⟩]
  obtain ⟨e, he, hey⟩ := exists_eq_mul_of_comp_eq L ι p hR t ⟨y₁, rfl⟩ ⟨y₂, ht₂⟩ h
  rw [hey]
  obtain ⟨e', he'⟩ := hE_inv t e he
  have he'f : e' ≫ ι ≫ f = t := by rw [← Category.assoc, he']; exact (L.inv t _).2
  obtain ⟨e'', he''⟩ := hE_norm t (L.inv t ⟨y₁, rfl⟩) e' he'f
  have he''f : e'' ≫ ι ≫ f = t := by rw [← Category.assoc, he'']; exact (L.mul t _ _).2
  have key : L.inv t (L.mul t ⟨e ≫ ι, he⟩ ⟨y₁, rfl⟩) = L.mul t ⟨e'' ≫ ι, he''f⟩ (L.inv t ⟨y₁, rfl⟩)
    := by
    have h1 : (⟨e' ≫ ι, he'f⟩ : SchemeHomOver t f) = L.inv t ⟨e ≫ ι, he⟩ := Subtype.ext he'
    have h2 : (⟨e'' ≫ ι, he''f⟩ : SchemeHomOver t f) =
        L.mul t (L.mul t (L.inv t ⟨y₁, rfl⟩) ⟨e' ≫ ι, he'f⟩) (L.inv t (L.inv t ⟨y₁, rfl⟩)) :=
          Subtype.ext he''
    rw [h2, h1]
    let : Group (SchemeHomOver t f) := L.pointGroup t
    change ((⟨e ≫ ι, he⟩ : SchemeHomOver t f) * ⟨y₁, rfl⟩)⁻¹ =
      ((⟨y₁, rfl⟩ : SchemeHomOver t f)⁻¹ * (⟨e ≫ ι, he⟩ : SchemeHomOver t f)⁻¹ * ((⟨y₁, rfl⟩ :
        SchemeHomOver t f)⁻¹)⁻¹) *
        (⟨y₁, rfl⟩ : SchemeHomOver t f)⁻¹
    group
  rw [key, p_act L ι p w t e'' _ he''f]

/-- The descended inversion morphism. -/
noncomputable def iP : P ⟶ P := EffectiveEpi.desc p (iJ L ≫ p) (cond_inv L ι g p hg w hR hE_inv
    hE_norm)

theorem p_iP : p ≫ iP L ι g p hg w hR hE_inv hE_norm = iJ L ≫ p :=
  EffectiveEpi.fac p (iJ L ≫ p) (cond_inv L ι g p hg w hR hE_inv hE_norm)

/-- The descended unit section. -/
noncomputable def eP : Spec (CommRingCat.of R) ⟶ P := eJ L ≫ p

omit w [Flat p] [Surjective p] [QuasiCompact p] hR hE_inv hE_norm in
theorem eP_over : eP L p ≫ g = 𝟙 _ := by rw [eP, Category.assoc, hg, eJ_over]

theorem iP_over : iP L ι g p hg w hR hE_inv hE_norm ≫ g = g := by
  have : Epi p := epi_p p
  rw [← cancel_epi p, ← Category.assoc, p_iP, Category.assoc, hg, iJ_over]

omit w [Flat p] [Surjective p] [QuasiCompact p] hR hE_inv hE_norm in
theorem over_p {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t f) : (x.1 ≫
    p) ≫ g = t := by
  rw [Category.assoc, hg, x.2]

omit w [Flat p] [Surjective p] [QuasiCompact p] hR hE_inv hE_norm in
theorem over_p' {T : Scheme.{u}} (a : T ⟶ J) : (a ≫ p) ≫ g = a ≫ f := by rw [Category.assoc, hg]

omit w [Flat p] [Surjective p] [QuasiCompact p] hR hE_inv hE_norm in
theorem over_eP {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : (t ≫ eP L p) ≫ g = t := by
  rw [Category.assoc, eP_over L g p hg, Category.comp_id]

omit w [Flat p] [Surjective p] [QuasiCompact p] hR hE_inv hE_norm in
theorem over_g_eP : (g ≫ eP L p) ≫ g = 𝟙 P ≫ g := by
  rw [Category.assoc, eP_over L g p hg, Category.comp_id, Category.id_comp]

theorem over_iP : iP L ι g p hg w hR hE_inv hE_norm ≫ g = 𝟙 P ≫ g := by rw [iP_over,
    Category.id_comp]

/-- The quotient map on the product. -/
noncomputable abbrev pp := oneP g p hg ≫ twoP g p hg

omit w [Flat p] [Surjective p] [QuasiCompact p] hR hE_inv hE_norm in
theorem lift_pp {T : Scheme.{u}} (a b : T ⟶ J) (h : a ≫ f = b ≫ f) :
    pullback.lift a b h ≫ pp g p hg =
      pullback.lift (a ≫ p) (b ≫ p) ((over_p' g p hg a).trans (h.trans
        (over_p' g p hg b).symm)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pp_fst, pullback.lift_fst_assoc, pullback.lift_fst]
  · rw [Category.assoc, pp_snd, pullback.lift_snd_assoc, pullback.lift_snd]

omit hE_inv in
theorem lift_p_mP {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    pullback.lift (x.1 ≫ p) (y.1 ≫ p) ((over_p g p hg x).trans (over_p g p hg y).symm) ≫ mP L ι g p
        hg w hR hE_norm =
      (L.mul t x y).1 ≫ p := by
  rw [← lift_pp g p hg x.1 y.1 (x.2.trans y.2.symm), Category.assoc, pp_mP,
    ← Category.assoc,
    comp_mJ L t _ (by rw [pullback.lift_fst_assoc]; exact x.2)]
  congr 3 <;> exact Subtype.ext (by simp only [pullback.lift_fst, pullback.lift_snd])

theorem p_iP_pt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    x.1 ≫ p ≫ iP L ι g p hg w hR hE_inv hE_norm = (L.inv t x).1 ≫ p := by
  rw [p_iP L ι g p hg w hR hE_inv hE_norm, ← Category.assoc, comp_iJ]

omit hE_inv in
theorem mP_swap (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t
    f), L.mul t x y = L.mul t y x) : pullback.lift (pullback.snd _ _) (pullback.fst _ _)
    pullback.condition.symm ≫ mP L ι g p hg w hR hE_norm =
    mP L ι g p hg w hR hE_norm := by
  have : Epi (oneP g p hg ≫ twoP g p hg) := epi_pp g p hg
  rw [← cancel_epi (oneP g p hg ≫ twoP g p hg)]
  have hsw : (oneP g p hg ≫ twoP g p hg) ≫ pullback.lift (pullback.snd _ _) (pullback.fst _ _)
    pullback.condition.symm =
      pullback.lift (pullback.snd f f ≫ p) (pullback.fst f f ≫ p)
        ((over_p' g p hg _).trans (pullback.condition.symm.trans (over_p' g p hg _).symm)) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]; exact pp_snd g p hg
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]; exact pp_fst g p hg
  rw [← Category.assoc, hsw]
  change _ = pp g p hg ≫ _
  rw [pp_mP]
  have h := lift_p_mP L ι g p hg w hR hE_norm (pullback.fst f f ≫ f) ⟨pullback.snd f f,
    pullback.condition.symm⟩ ⟨pullback.fst f f, rfl⟩
  rw [h, hcomm]
  rfl

omit hE_inv in
theorem one_mul_id : pullback.lift (g ≫ eP L p) (𝟙 P) (over_g_eP L g p hg) ≫
    mP L ι g p hg w hR hE_norm = 𝟙 P := by
  have : Epi p := epi_p p
  rw [← cancel_epi p, Category.comp_id p, ← Category.assoc]
  have h1 : p ≫ pullback.lift (g ≫ eP L p) (𝟙 P) (over_g_eP L g p hg) =
      pullback.lift ((L.one f).1 ≫ p) ((⟨𝟙 J, Category.id_comp f⟩ : SchemeHomOver f f).1 ≫ p)
        ((over_p g p hg _).trans (over_p g p hg
          _).symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc, hg, eP, ←
        Category.assoc, comp_eJ]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
      exact (Category.comp_id p).trans (Category.id_comp p).symm
  rw [h1, lift_p_mP L ι g p hg w hR hE_norm f (L.one f) ⟨𝟙 J, Category.id_comp f⟩, L.one_mul]
  exact Category.id_comp _

omit hE_inv in
theorem mul_one_id : pullback.lift (𝟙 P) (g ≫ eP L p) (over_g_eP L g p hg).symm ≫ mP L ι g p hg w hR
    hE_norm = 𝟙 P := by
  have : Epi p := epi_p p
  rw [← cancel_epi p, Category.comp_id p, ← Category.assoc]
  have h1 : p ≫ pullback.lift (𝟙 P) (g ≫ eP L p) (over_g_eP L g p hg).symm =
      pullback.lift ((⟨𝟙 J, Category.id_comp f⟩ : SchemeHomOver f f).1 ≫ p) ((L.one f).1 ≫ p)
        ((over_p g p hg _).trans (over_p g p hg
          _).symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      exact (Category.comp_id p).trans (Category.id_comp p).symm
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, hg, eP, ←
        Category.assoc, comp_eJ]
  rw [h1, lift_p_mP L ι g p hg w hR hE_norm f ⟨𝟙 J, Category.id_comp f⟩ (L.one f), L.mul_one]
  exact Category.id_comp _

theorem inv_mul_id : pullback.lift (iP L ι g p hg w hR hE_inv hE_norm) (𝟙 P) (over_iP L ι g p hg w
    hR hE_inv hE_norm) ≫ mP L ι g p hg w hR hE_norm =
    g ≫ eP L p := by
  have : Epi p := epi_p p
  rw [← cancel_epi p, ← Category.assoc, ← Category.assoc, hg]
  have h1 : p ≫ pullback.lift (iP L ι g p hg w hR hE_inv hE_norm) (𝟙 P) (over_iP L ι g p hg w hR
    hE_inv hE_norm) =
      pullback.lift ((L.inv f ⟨𝟙 J, Category.id_comp f⟩).1 ≫ p) ((⟨𝟙 J, Category.id_comp f⟩ :
        SchemeHomOver f f).1 ≫ p)
        ((over_p g p hg _).trans (over_p g p hg
          _).symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, p_iP L ι g p hg w hR hE_inv hE_norm,
        iJ]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
      exact (Category.comp_id p).trans (Category.id_comp p).symm
  rw [h1, lift_p_mP L ι g p hg w hR hE_norm f (L.inv f ⟨𝟙 J, Category.id_comp f⟩) ⟨𝟙 J,
    Category.id_comp f⟩, L.inv_mul_cancel, eP,
    ← Category.assoc, comp_eJ]

omit hE_inv in
/-- The left-associated descended product. -/
noncomputable def α3 : pullback (pullback.fst (g) (g) ≫ g) (g) ⟶ P :=
  pullback.lift (pullback.fst _ _ ≫ mP L ι g p hg w hR hE_norm) (pullback.snd _ _)
    (by rw [Category.assoc, mP_over]; exact pullback.condition) ≫ mP L ι g p hg w hR hE_norm

omit hE_inv in
/-- The right-associated descended product. -/
noncomputable def β3 : pullback (pullback.fst (g) (g) ≫ g) (g) ⟶ P :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _)
      (by rw [Category.assoc]; exact (congrArg (fun k => pullback.fst _ _ ≫ k)
        pullback.condition).symm.trans pullback.condition) ≫
      mP L ι g p hg w hR hE_norm)
    (by rw [Category.assoc, Category.assoc, mP_over, pullback.lift_fst_assoc]; exact congrArg (fun k
      => pullback.fst _ _ ≫ k) pullback.condition) ≫
  mP L ι g p hg w hR hE_norm

/-- The quotient map on the triple product. -/
noncomputable def q3 : pullback (pullback.fst f f ≫ f) f ⟶ pullback (pullback.fst (g) (g) ≫ g) (g)
    :=
  pullback.map _ _ _ _ (pp g p hg) p (𝟙 _)
    (by rw [Category.comp_id, ← Category.assoc, pp_fst, Category.assoc, hg]) (by rw
      [Category.comp_id, hg])

omit w [QuasiCompact p] hR hE_inv hE_norm in
theorem epi_q3 : Epi (q3 g p hg) := by
  have hflat : Flat (pp g p hg) := inferInstance
  have hsurj : Surjective (pp g p hg) := inferInstance
  have e₁ : pullback.fst f f ≫ f = pp g p hg ≫ pullback.fst (g) (g) ≫ g := by
    rw [← Category.assoc, pp_fst, Category.assoc, hg]
  have e₂ : f = p ≫ g := (hg).symm
  have : Flat (q3 g p hg) := MorphismProperty.pullbackMap (P := @Flat) hflat (inferInstance : Flat
    p) e₁ e₂
  have hmult : MorphismProperty.IsMultiplicative
      (@Surjective : MorphismProperty Scheme.{u}) := inferInstance
  have : MorphismProperty.IsStableUnderComposition
      (@Surjective : MorphismProperty Scheme.{u}) := hmult.toIsStableUnderComposition
  have : Surjective (q3 g p hg) := MorphismProperty.pullbackMap
    (P := (@Surjective : MorphismProperty Scheme.{u})) hsurj
    (inferInstance : Surjective p) e₁ e₂
  exact Flat.epi_of_flat_of_surjective _

omit w [Flat p] [Surjective p] [QuasiCompact p] hR hE_inv hE_norm in
@[reassoc] theorem q3_fst : q3 g p hg ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pp g p hg :=
    pullback.lift_fst _ _ _
omit w [Flat p] [Surjective p] [QuasiCompact p] hR hE_inv hE_norm in
@[reassoc] theorem q3_snd : q3 g p hg ≫ pullback.snd _ _ = pullback.snd _ _ ≫ p := pullback.lift_snd
    _ _ _

omit hE_inv in
theorem pp_mP' : oneP g p hg ≫ twoP g p hg ≫ mP L ι g p hg w hR hE_norm = mJ L ≫ p := by
  rw [← Category.assoc]; exact pp_mP L ι g p hg w hR hE_norm
omit w [Flat p] [Surjective p] [QuasiCompact p] hR hE_inv hE_norm in
theorem pp_fst' : oneP g p hg ≫ twoP g p hg ≫ pullback.fst _ _ = pullback.fst f f ≫ p := by
  rw [← Category.assoc]; exact pp_fst g p hg
omit w [Flat p] [Surjective p] [QuasiCompact p] hR hE_inv hE_norm in
theorem pp_snd' : oneP g p hg ≫ twoP g p hg ≫ pullback.snd _ _ = pullback.snd f f ≫ p := by
  rw [← Category.assoc]; exact pp_snd g p hg

/-- The structural map of the triple product. -/
noncomputable abbrev t3 : pullback (pullback.fst f f ≫ f) f ⟶ Spec (CommRingCat.of R) :=
    pullback.fst _ _ ≫ pullback.fst f f ≫ f

/-- The first relative point of the triple product. -/
noncomputable abbrev X3 : SchemeHomOver (t3 (f := f)) f := ⟨pullback.fst _ _ ≫ pullback.fst f f,
    rfl⟩
/-- The second relative point of the triple product. -/
noncomputable abbrev Y3 : SchemeHomOver (t3 (f := f)) f :=
  ⟨pullback.fst _ _ ≫ pullback.snd f f, by rw [Category.assoc]; exact (congrArg (fun k =>
    pullback.fst _ _ ≫ k) pullback.condition).symm⟩
/-- The third relative point of the triple product. -/
noncomputable abbrev Z3 : SchemeHomOver (t3 (f := f)) f := ⟨pullback.snd _ _,
    pullback.condition.symm⟩

omit hE_inv in
theorem q3_α3 : q3 g p hg ≫ α3 L ι g p hg w hR hE_norm = (L.mul t3 (L.mul t3 X3 Y3) Z3).1 ≫ p
    := by
  have hin : q3 g p hg ≫ pullback.lift (pullback.fst _ _ ≫ mP L ι g p hg w hR hE_norm)
    (pullback.snd _ _)
        (by rw [Category.assoc, mP_over]; exact pullback.condition) =
      pullback.lift ((L.mul t3 X3 Y3).1 ≫ p) ((Z3 (f := f)).1 ≫ p) ((over_p g p hg _).trans (over_p
          g p hg _).symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, q3_fst_assoc g p hg, pp_mP' L ι g p
        hg w hR hE_norm, ← Category.assoc,
        comp_mJ L t3 _ rfl]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, q3_snd g p hg]
  rw [α3, ← Category.assoc, hin, lift_p_mP]

omit hE_inv in
theorem q3_β3 : q3 g p hg ≫ β3 L ι g p hg w hR hE_norm = (L.mul t3 X3 (L.mul t3 Y3 Z3)).1 ≫ p
    := by
  have hin : q3 g p hg ≫ pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
      (pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _)
        (by rw [Category.assoc]; exact (congrArg (fun k => pullback.fst _ _ ≫ k)
          pullback.condition).symm.trans pullback.condition) ≫
        mP L ι g p hg w hR hE_norm)
      (by rw [Category.assoc, Category.assoc, mP_over, pullback.lift_fst_assoc]; exact congrArg (fun
        k => pullback.fst _ _ ≫ k) pullback.condition) =
      pullback.lift ((X3 (f := f)).1 ≫ p) ((L.mul t3 Y3 Z3).1 ≫ p) ((over_p g p hg _).trans (over_p
          g p hg _).symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, q3_fst_assoc g p hg, pp_fst' g p hg,
        Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc]
      have h2 : q3 g p hg ≫ pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _)
            (by rw [Category.assoc]; exact (congrArg (fun k => pullback.fst _ _ ≫ k)
              pullback.condition).symm.trans pullback.condition) =
          pullback.lift ((Y3 (f := f)).1 ≫ p) ((Z3 (f := f)).1 ≫ p) ((over_p g p hg _).trans (over_p
              g p hg _).symm) := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, q3_fst_assoc g p hg, pp_snd' g p
            hg, Category.assoc]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, q3_snd g p hg]
      rw [h2, lift_p_mP]
  rw [β3, ← Category.assoc, hin, lift_p_mP]

omit hE_inv in
theorem α3_eq_β3 : α3 L ι g p hg w hR hE_norm = β3 L ι g p hg w hR hE_norm := by
  have : Epi (q3 g p hg) := epi_q3 g p hg
  rw [← cancel_epi (q3 g p hg), q3_α3, q3_β3, L.mul_assoc]

/-- The point of a product from two relative points. -/
noncomputable abbrev pr2 {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (u v : SchemeHomOver t
    (g)) :
    T ⟶ pullback (g) (g) :=
  pullback.lift u.1 v.1 (u.2.trans v.2.symm)

omit hg w hR hE_inv hE_norm [Flat p] [Surjective p] [QuasiCompact p] in
private theorem pr2_fst {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (u v : SchemeHomOver t g) : pr2 g u v ≫ pullback.fst g g = u.1 :=
  pullback.lift_fst _ _ _

omit hg w hR hE_inv hE_norm [Flat p] [Surjective p] [QuasiCompact p] in
private theorem pr2_snd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (u v : SchemeHomOver t g) : pr2 g u v ≫ pullback.snd g g = v.1 :=
  pullback.lift_snd _ _ _

/-- The descended relative group law. -/
noncomputable def lawP : RelativeGroupLaw R (g) where
  mul t u v := ⟨pr2 g u v ≫ mP L ι g p hg w hR hE_norm, by
    rw [Category.assoc, mP_over L ι g p hg w hR hE_norm, pullback.lift_fst_assoc]
    exact u.2⟩
  one t := ⟨t ≫ eP L p, over_eP L g p hg t⟩
  inv t u := ⟨u.1 ≫ iP L ι g p hg w hR hE_inv hE_norm, by
    rw [Category.assoc, iP_over L ι g p hg w hR hE_inv hE_norm]
    exact u.2⟩
  mul_assoc t u v x := by
    apply Subtype.ext
    have hux : pr2 g u v ≫ (pullback.fst g g ≫ g) = x.1 ≫ g := by
      rw [pullback.lift_fst_assoc]
      exact u.2.trans x.2.symm
    have hmux : (pr2 g u v ≫ mP L ι g p hg w hR hE_norm) ≫ g = x.1 ≫ g := by
      rw [Category.assoc, mP_over, pullback.lift_fst_assoc]
      exact u.2.trans x.2.symm
    have humvx : u.1 ≫ g =
        (pullback.lift v.1 x.1 (v.2.trans x.2.symm) ≫ mP L ι g p hg w hR hE_norm) ≫ g := by
      rw [Category.assoc, mP_over, pullback.lift_fst_assoc]
      exact u.2.trans v.2.symm
    have h3 : pullback.lift (pr2 g u v) x.1 hux ≫ α3 L ι g p hg w hR hE_norm =
        pullback.lift (pr2 g u v) x.1 hux ≫
          β3 L ι g p hg w hR hE_norm := by
      rw [α3_eq_β3]
    have hl : pullback.lift (pr2 g u v) x.1 hux ≫ α3 L ι g p hg w hR hE_norm =
        pullback.lift (pr2 g u v ≫ mP L ι g p hg w hR hE_norm) x.1
          hmux ≫ mP L ι g p hg w hR hE_norm := by
      rw [α3, ← Category.assoc]; congr 1
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
    have hr : pullback.lift (pr2 g u v) x.1 hux ≫ β3 L ι g p hg w hR hE_norm =
        pullback.lift u.1 (pullback.lift v.1 x.1 (v.2.trans x.2.symm) ≫ mP L ι g p hg w hR hE_norm)
          humvx ≫ mP L ι g p hg w hR hE_norm := by
      rw [β3, ← Category.assoc]; congr 1
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst,
          pullback.lift_fst]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc]; congr 1
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd,
            pullback.lift_fst]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
    change pullback.lift (pr2 g u v ≫ mP L ι g p hg w hR hE_norm) x.1 _ ≫ mP L ι g p hg w hR hE_norm
        =
      pullback.lift u.1 (pullback.lift v.1 x.1 _ ≫ mP L ι g p hg w hR hE_norm) _ ≫ mP L ι g p hg w
          hR hE_norm
    rw [← hl, ← hr, h3]
  one_mul t u := by
    apply Subtype.ext
    change pullback.lift (t ≫ eP L p) u.1 _ ≫ mP L ι g p hg w hR hE_norm = u.1
    have h : pullback.lift (t ≫ eP L p) u.1 ((over_eP L g p hg t).trans
      u.2.symm) =
        u.1 ≫ pullback.lift (g ≫ eP L p) (𝟙 P) (over_g_eP L g p hg) := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, u.2]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [h, Category.assoc, one_mul_id, Category.comp_id]
  mul_one t u := by
    apply Subtype.ext
    change pullback.lift u.1 (t ≫ eP L p) _ ≫ mP L ι g p hg w hR hE_norm = u.1
    have h : pullback.lift u.1 (t ≫ eP L p) (u.2.trans (over_eP L g p hg
      t).symm) =
        u.1 ≫ pullback.lift (𝟙 P) (g ≫ eP L p) (over_g_eP L g p hg).symm := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, Category.comp_id]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc, u.2]
    rw [h, Category.assoc, mul_one_id, Category.comp_id]
  inv_mul_cancel t u := by
    apply Subtype.ext
    change pullback.lift (u.1 ≫ iP L ι g p hg w hR hE_inv hE_norm) u.1 _ ≫ mP L ι g p hg w hR
        hE_norm = t ≫ eP L p
    have h : pullback.lift (u.1 ≫ iP L ι g p hg w hR hE_inv hE_norm) u.1 (by rw [Category.assoc,
      iP_over L ι g p hg w hR hE_inv hE_norm]) =
        u.1 ≫ pullback.lift (iP L ι g p hg w hR hE_inv hE_norm) (𝟙 P) (over_iP L ι g p hg w hR
          hE_inv hE_norm) := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [h, Category.assoc, inv_mul_id, ← Category.assoc, u.2]
  mul_natural t t' ψ hψ u v := by
    apply Subtype.ext
    change ψ ≫ pr2 g u v ≫ mP L ι g p hg w hR hE_norm =
      pr2 g (GoodReductionJacobian.schemeHomOverComp ψ hψ u)
        (GoodReductionJacobian.schemeHomOverComp ψ hψ v) ≫ mP L ι g p hg w hR hE_norm
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, pr2_fst, GoodReductionJacobian.schemeHomOverComp_coe]
    · simp only [Category.assoc, pr2_snd, GoodReductionJacobian.schemeHomOverComp_coe]

theorem lawP_mul_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t (g))
    :
    ((lawP L ι g p hg w hR hE_inv hE_norm).mul t u v).1 = pr2 g u v ≫ mP L ι g p hg w hR hE_norm :=
        rfl

theorem lawP_one_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : ((lawP L ι g p hg w hR
    hE_inv hE_norm).one t).1 = t ≫ eP L p := rfl

theorem hom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    (⟨(L.mul t x y).1 ≫ p, by rw [Category.assoc, hg, (L.mul t x y).2]⟩ : SchemeHomOver t (g)) =
      (lawP L ι g p hg w hR hE_inv hE_norm).mul t ⟨x.1 ≫ p, by rw [Category.assoc, hg, x.2]⟩ ⟨y.1 ≫
        p, by rw [Category.assoc, hg, y.2]⟩ := by
  apply Subtype.ext
  rw [lawP_mul_coe]
  exact (lift_p_mP L ι g p hg w hR hE_norm t x y).symm

theorem comm (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t
    f), L.mul t x y = L.mul t y x)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t (g)) :
    (lawP L ι g p hg w hR hE_inv hE_norm).mul t u v = (lawP L ι g p hg w hR hE_inv hE_norm).mul t v
      u := by
  apply Subtype.ext
  rw [lawP_mul_coe, lawP_mul_coe]
  conv_rhs => rw [← mP_swap L ι g p hg w hR hE_norm hcomm, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · change pullback.lift u.1 v.1 _ ≫ pullback.fst _ _ = (pullback.lift v.1 u.1 _ ≫ pullback.lift _ _
      _) ≫ pullback.fst _ _
    rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_snd]
  · change pullback.lift u.1 v.1 _ ≫ pullback.snd _ _ = (pullback.lift v.1 u.1 _ ≫ pullback.lift _ _
      _) ≫ pullback.snd _ _
    rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_fst]

theorem ker {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    (⟨x.1 ≫ p, by rw [Category.assoc, hg, x.2]⟩ : SchemeHomOver t (g)) = (lawP L ι g p hg w hR
      hE_inv hE_norm).one t ↔
      ∃ e : T ⟶ E, e ≫ ι = x.1 := by
  constructor
  · intro h
    have h' : x.1 ≫ p = (L.one t).1 ≫ p := by
      have := congrArg Subtype.val h
      rw [lawP_one_coe, eP] at this
      have e2 : (t ≫ eJ L) ≫ p = (L.one t).1 ≫ p := by rw [comp_eJ]
      exact (this.trans (Category.assoc _ _ _).symm).trans e2
    let φ := hR.lift (L.one t).1 x.1 h'.symm
    have hφs : φ ≫ pullback.snd (ι ≫ f) f = (L.one t).1 := hR.lift_fst _ _ _
    have hφt : φ ≫ L.action ι = x.1 := hR.lift_snd _ _ _
    have hbase : φ ≫ RelativeGroupLaw.actionSource f ι = t := by
      change φ ≫ (pullback.snd _ _ ≫ f) = t
      rw [← Category.assoc, hφs]; exact (L.one t).2
    refine ⟨φ ≫ pullback.fst _ _, ?_⟩
    rw [comp_action' L ι t φ hbase] at hφt
    have hone : (⟨φ ≫ pullback.snd (ι ≫ f) f, by rw [← hbase, Category.assoc]⟩ : SchemeHomOver t f)
      = L.one t := Subtype.ext hφs
    rw [hone, L.mul_one] at hφt
    rw [Category.assoc]; exact hφt
  · rintro ⟨e, he⟩
    apply Subtype.ext
    change x.1 ≫ p = ((lawP L ι g p hg w hR hE_inv hE_norm).one t).1
    rw [lawP_one_coe, eP, ← Category.assoc t, comp_eJ]
    have hef : e ≫ ι ≫ f = t := by rw [← Category.assoc, he, x.2]
    have h := p_act L ι p w t e (L.one t) hef
    rw [L.mul_one] at h
    rw [← h]
    congr 1
    exact he.symm

end Descent

end Laws

end AbelianVarieties.NOSProofs.QuotientGroupLaw

namespace GoodReductionJacobian.RelativeGroupLaw

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AbelianVarieties.NOSProofs.QuotientGroupLaw.Laws

theorem exists_relativeGroupLaw_quotient_of_isPullback_action_of_surjective
    {R : Type u} [CommRing R] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)} (L :
      RelativeGroupLaw R f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw R (i ≫ f))
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (hnormal : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f)
      (n : SchemeHomOver t (i ≫ f)), ∃ n' : SchemeHomOver t (i ≫ f),
        NeronModelInfra.schemeHomOverComp n' (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (L.mul t x (NeronModelInfra.schemeHomOverComp n (⟨i, rfl⟩ : SchemeHomOver (i ≫ f)
            f)))
            (L.inv t x))
    {Q : Scheme.{u}} {fQ : Q ⟶ Spec (CommRingCat.of R)} (q : SchemeHomOver f fQ)
    [Flat q.1] [LocallyOfFinitePresentation q.1] [Surjective q.1] [QuasiCompact q.1]
    (w : CategoryTheory.Limits.pullback.snd (i ≫ f) f ≫ q.1 = L.action i ≫ q.1)
    (hR : IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f) (L.action i) q.1 q.1)
    (_hcoeq : IsColimit (Cofork.ofπ q.1 w)) :
    ∃ LQ : RelativeGroupLaw R fQ,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
          LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q))
            ∧
      (L.IsCommutative → LQ.IsCommutative) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        NeronModelInfra.schemeHomOverComp x q = LQ.one t ↔
          ∃ y : SchemeHomOver t (i ≫ f),
            NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = x) := by
  let iPt : SchemeHomOver (i ≫ f) f := ⟨i, rfl⟩
  have hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      NeronModelInfra.schemeHomOverComp (LN.one t) iPt = L.one t := by
    intro T t
    let : Group (SchemeHomOver t f) := L.pointGroup t
    have h := hi t (LN.one t) (LN.one t)
    rw [LN.one_mul] at h
    have h' : (NeronModelInfra.schemeHomOverComp (LN.one t) iPt : SchemeHomOver t f) =
        NeronModelInfra.schemeHomOverComp (LN.one t) iPt * NeronModelInfra.schemeHomOverComp (LN.one
          t) iPt := h
    exact left_eq_mul.mp h'
  have hinv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.inv t n) iPt = L.inv t
        (NeronModelInfra.schemeHomOverComp n iPt) := by
    intro T t n
    let : Group (SchemeHomOver t f) := L.pointGroup t
    have h := hi t (LN.inv t n) n
    rw [LN.inv_mul_cancel, hone] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have hE_inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (e : T ⟶ N) (he : e ≫ i ≫ f =
    t),
      ∃ e' : T ⟶ N, e' ≫ i = (L.inv t ⟨e ≫ i, he⟩).1 := by
    intro T t e he
    refine ⟨(LN.inv t ⟨e, he⟩).1, ?_⟩
    have := congrArg Subtype.val (hinv t ⟨e, he⟩)
    exact this
  have hE_norm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (e : T
    ⟶ N)
      (he : e ≫ i ≫ f = t), ∃ e' : T ⟶ N, e' ≫ i = (L.mul t (L.mul t x ⟨e ≫ i, he⟩) (L.inv t x)).1
        := by
    intro T t x e he
    obtain ⟨n', hn'⟩ := hnormal t x ⟨e, he⟩
    refine ⟨n'.1, ?_⟩
    have := congrArg Subtype.val hn'
    exact this
  refine ⟨lawP L i fQ q.1 q.2 w hR hE_inv hE_norm, ?_, ?_, ?_⟩
  · intro T t x y
    exact hom L i fQ q.1 q.2 w hR hE_inv hE_norm t x y
  · intro hc T t u v
    exact comm L i fQ q.1 q.2 w hR hE_inv hE_norm (fun t x y => hc t x y) t u v
  · intro T t x
    rw [show NeronModelInfra.schemeHomOverComp x q = (⟨x.1 ≫ q.1, by rw [Category.assoc, q.2, x.2]⟩
      : SchemeHomOver t fQ) from rfl,
      ker L i fQ q.1 q.2 w hR hE_inv hE_norm t x]
    constructor
    · rintro ⟨e, he⟩
      have hef : e ≫ i ≫ f = t := by rw [← Category.assoc, he, x.2]
      exact ⟨⟨e, hef⟩, Subtype.ext he⟩
    · rintro ⟨y, hy⟩
      exact ⟨y.1, congrArg Subtype.val hy⟩

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_forall_exists_opens_saturated_fppf_quotient_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.QuotientTranslationCover

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace TranslationCover

open AbelianVarieties.NOSProofs.TranslationAutomorphisms.Translations
open scoped AbelianVarieties.NOSProofs.TranslationAutomorphisms.Translations

variable {k : Type u} [CommRing k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L :
    RelativeGroupLaw k f)

/-- Translation on the group factor of the action source. -/
def Rt {N : Scheme.{u}} (i : N ⟶ G) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    pullback (i ≫ f) f ⟶ pullback (i ≫ f) f :=
  pullback.lift (pullback.fst (i ≫ f) f) (pullback.snd (i ≫ f) f ≫ rt L a)
    (by rw [Category.assoc, rt_over, pullback.condition])

@[scoped simp] theorem Rt_fst {N : Scheme.{u}} (i : N ⟶ G) (a : SchemeHomOver (𝟙 (Spec
    (CommRingCat.of k))) f) :
    Rt L i a ≫ pullback.fst (i ≫ f) f = pullback.fst (i ≫ f) f := pullback.lift_fst _ _ _

@[scoped simp] theorem Rt_snd {N : Scheme.{u}} (i : N ⟶ G) (a : SchemeHomOver (𝟙 (Spec
    (CommRingCat.of k))) f) :
    Rt L i a ≫ pullback.snd (i ≫ f) f = pullback.snd (i ≫ f) f ≫ rt L a := pullback.lift_snd _ _ _

theorem Rt_action {N : Scheme.{u}} (i : N ⟶ G) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    Rt L i a ≫ L.action i = L.action i ≫ rt L a := by
  have hsrc : Rt L i a ≫ RelativeGroupLaw.actionSource f i = RelativeGroupLaw.actionSource f i := by
    rw [RelativeGroupLaw.actionSource, ← Category.assoc, Rt_snd, Category.assoc, rt_over]
  have hR : L.action i ≫ rt L a =
      (L.mul (RelativeGroupLaw.actionSource f i) (L.actionFstPoint i)
        (L.mul _ (L.actionSndPoint i) (const a _))).1 := by
    rw [RelativeGroupLaw.action_def, comp_rt, L.mul_assoc]
  have h1 : schemeHomOverComp (Rt L i a) hsrc (L.actionFstPoint i) = L.actionFstPoint i := by
    apply Subtype.ext
    change Rt L i a ≫ (pullback.fst (i ≫ f) f ≫ i) = pullback.fst (i ≫ f) f ≫ i
    rw [← Category.assoc, Rt_fst]
  have h2 : schemeHomOverComp (Rt L i a) hsrc (L.actionSndPoint i) =
      L.mul _ (L.actionSndPoint i) (const a _) := by
    apply Subtype.ext
    change Rt L i a ≫ pullback.snd (i ≫ f) f = (L.mul _ (L.actionSndPoint i) (const a _)).1
    rw [Rt_snd, ← comp_rt]; rfl
  have hL : Rt L i a ≫ L.action i =
      (schemeHomOverComp (Rt L i a) hsrc (L.mul _ (L.actionFstPoint i) (L.actionSndPoint i))).1 :=
        rfl
  rw [hL, L.mul_natural _ _ (Rt L i a) hsrc, h1, h2, hR]

theorem Rt_mul {N : Scheme.{u}} (i : N ⟶ G) (a b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    Rt L i a ≫ Rt L i b = Rt L i (L.mul (𝟙 _) a b) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Rt_fst, Rt_fst, Rt_fst]
  · rw [Category.assoc, Rt_snd, ← Category.assoc, Rt_snd, Category.assoc, rt_mul, Rt_snd]

theorem Rt_one {N : Scheme.{u}} (i : N ⟶ G) : Rt L i (L.one (𝟙 _)) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Rt_fst, Category.id_comp]
  · rw [Rt_snd, rt_one, Category.id_comp, Category.comp_id]

/-- Translation as an automorphism of the action source. -/
def RtIso {N : Scheme.{u}} (i : N ⟶ G) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    pullback (i ≫ f) f ≅ pullback (i ≫ f) f where
  hom := Rt L i a
  inv := Rt L i (L.inv (𝟙 _) a)
  hom_inv_id := by rw [Rt_mul, L.mul_inv_cancel, Rt_one]
  inv_hom_id := by rw [Rt_mul, L.inv_mul_cancel, Rt_one]

scoped instance {N : Scheme.{u}} (i : N ⟶ G) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    IsIso (Rt L i a) := (RtIso L i a).isIso_hom

section transport

variable {N : Scheme.{u}} (i : N ⟶ G) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
  (U : G.Opens) (hU : pullback.snd (i ≫ f) f ⁻¹ᵁ U = L.action i ⁻¹ᵁ U)

include hU in
theorem sat_preimage : pullback.snd (i ≫ f) f ⁻¹ᵁ (rt L a ⁻¹ᵁ U) = L.action i ⁻¹ᵁ (rt L a ⁻¹ᵁ U)
    := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, ← Rt_snd, ← Rt_action,
    Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, hU]

theorem preimage_Rt : pullback.snd (i ≫ f) f ⁻¹ᵁ (rt L a ⁻¹ᵁ U) = Rt L i a ⁻¹ᵁ (pullback.snd (i ≫ f)
    f ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, Rt_snd]

/-- The induced isomorphism of translated open action charts. -/
def E : ((pullback.snd (i ≫ f) f ⁻¹ᵁ (rt L a ⁻¹ᵁ U)) : Scheme.{u}) ⟶ ((pullback.snd (i ≫ f) f ⁻¹ᵁ U)
    : Scheme.{u}) :=
  ((pullback (i ≫ f) f).isoOfEq (preimage_Rt L i a U)).hom ≫ (Rt L i a ∣_ (pullback.snd (i ≫ f) f
    ⁻¹ᵁ U))

scoped instance : IsIso (E L i a U) := by unfold E; infer_instance

@[reassoc]
theorem E_ι : E L i a U ≫ (pullback.snd (i ≫ f) f ⁻¹ᵁ U).ι = (pullback.snd (i ≫ f) f ⁻¹ᵁ (rt L a ⁻¹ᵁ
    U)).ι ≫ Rt L i a := by
  rw [E, Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]

theorem sq1 : E L i a U ≫ (pullback.snd (i ≫ f) f ∣_ U) = (pullback.snd (i ≫ f) f ∣_ (rt L a ⁻¹ᵁ U))
    ≫ (rt L a ∣_ U) := by
  rw [← cancel_mono U.ι, Category.assoc, Category.assoc, morphismRestrict_ι, E_ι_assoc, Rt_snd,
    morphismRestrict_ι,
    morphismRestrict_ι_assoc]

theorem sq2 (hW : pullback.snd (i ≫ f) f ⁻¹ᵁ (rt L a ⁻¹ᵁ U) = L.action i ⁻¹ᵁ (rt L a ⁻¹ᵁ U)) :
    E L i a U ≫ (((pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ U)) =
      (((pullback (i ≫ f) f).isoOfEq hW).hom ≫ (L.action i ∣_ (rt L a ⁻¹ᵁ U))) ≫ (rt L a ∣_ U) := by
  rw [← cancel_mono U.ι]
  simp only [Category.assoc, morphismRestrict_ι]
  rw [Scheme.isoOfEq_hom_ι_assoc, E_ι_assoc, Rt_action, morphismRestrict_ι_assoc,
    Scheme.isoOfEq_hom_ι_assoc]

theorem transport (hW : pullback.snd (i ≫ f) f ⁻¹ᵁ (rt L a ⁻¹ᵁ U) = L.action i ⁻¹ᵁ (rt L a ⁻¹ᵁ U))
    {Y : Scheme.{u}} (p : (U : Scheme.{u}) ⟶ Y)
    (hco : (pullback.snd (i ≫ f) f ∣_ U) ≫ p = (((pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i
      ∣_ U)) ≫ p)
    [Flat p] [LocallyOfFinitePresentation p] [QuasiCompact p] [Surjective p]
    (hpb : IsPullback (pullback.snd (i ≫ f) f ∣_ U) (((pullback (i ≫ f) f).isoOfEq hU).hom ≫
      (L.action i ∣_ U)) p p) :
    ((pullback.snd (i ≫ f) f ∣_ (rt L a ⁻¹ᵁ U)) ≫ ((rt L a ∣_ U) ≫ p) =
        (((pullback (i ≫ f) f).isoOfEq hW).hom ≫ (L.action i ∣_ (rt L a ⁻¹ᵁ U))) ≫ ((rt L a ∣_ U) ≫
          p)) ∧
      Flat ((rt L a ∣_ U) ≫ p) ∧ LocallyOfFinitePresentation ((rt L a ∣_ U) ≫ p) ∧ QuasiCompact ((rt
        L a ∣_ U) ≫ p) ∧
      Surjective ((rt L a ∣_ U) ≫ p) ∧
      IsPullback (pullback.snd (i ≫ f) f ∣_ (rt L a ⁻¹ᵁ U)) (((pullback (i ≫ f) f).isoOfEq hW).hom ≫
        (L.action i ∣_ (rt L a ⁻¹ᵁ U)))
        ((rt L a ∣_ U) ≫ p) ((rt L a ∣_ U) ≫ p) := by
  have s1 := sq1 L i a U
  have s2 := sq2 L i a U hU hW
  refine ⟨?_, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  · rw [← Category.assoc, ← s1, Category.assoc, hco, ← Category.assoc, s2, Category.assoc]
  · refine IsPullback.of_iso hpb (asIso (E L i a U)).symm (asIso (rt L a ∣_ U)).symm (asIso (rt L a
      ∣_ U)).symm (Iso.refl Y)
      ?_ ?_ ?_ ?_
    · rw [Iso.symm_hom, Iso.symm_hom, asIso_inv, asIso_inv, IsIso.comp_inv_eq, Category.assoc,
        IsIso.eq_inv_comp, s1]
    · rw [Iso.symm_hom, Iso.symm_hom, asIso_inv, asIso_inv, IsIso.comp_inv_eq, Category.assoc,
        IsIso.eq_inv_comp, s2]
    · rw [Iso.refl_hom, Iso.symm_hom, asIso_inv, Category.comp_id, IsIso.inv_hom_id_assoc]
    · rw [Iso.refl_hom, Iso.symm_hom, asIso_inv, Category.comp_id, IsIso.inv_hom_id_assoc]

end transport

end TranslationCover

end

end AbelianVarieties.NOSProofs.QuotientTranslationCover

namespace GoodReductionJacobian.RelativeGroupLaw

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AbelianVarieties.NOSProofs.QuotientTranslationCover.TranslationCover
open AbelianVarieties.NOSProofs.TranslationAutomorphisms.Translations
open scoped AbelianVarieties.NOSProofs.TranslationAutomorphisms.Translations

theorem forall_exists_opens_saturated_fppf_quotient_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (L : RelativeGroupLaw k f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i]
    (U : G.Opens) (hU : CategoryTheory.Limits.pullback.snd (i ≫ f) f ⁻¹ᵁ U = L.action i ⁻¹ᵁ U)
      [Nonempty (U.toScheme)]
    (hloc : ∃ (Y : Scheme.{u}) (p : (U).toScheme ⟶ Y),
        (CategoryTheory.Limits.pullback.snd (i ≫ f) f ∣_ U) ≫ p =
          (((CategoryTheory.Limits.pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ U)) ≫ p ∧
        Flat p ∧ LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ Surjective p ∧
        IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f ∣_ U)
          (((CategoryTheory.Limits.pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ U)) p p) :
    ∀ x : G, ∃ (W : G.Opens) (hU : CategoryTheory.Limits.pullback.snd (i ≫ f) f ⁻¹ᵁ W = L.action i
      ⁻¹ᵁ W), x ∈ W ∧
      ∃ (Y : Scheme.{u}) (p : (W).toScheme ⟶ Y),
        (CategoryTheory.Limits.pullback.snd (i ≫ f) f ∣_ W) ≫ p =
          (((CategoryTheory.Limits.pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ W)) ≫ p ∧
        Flat p ∧ LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ Surjective p ∧
        IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f ∣_ W)
          (((CategoryTheory.Limits.pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ W)) p p
            := by
  classical
  intro x
  have : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨z, hzcl, hzc⟩ := nonempty_inter_closedPoints (Z := closure {x}) ⟨x, subset_closure rfl⟩
    isClosed_closure.isLocallyClosed
  rw [mem_closedPoints_iff] at hzc
  obtain ⟨u₀⟩ := (inferInstance : Nonempty (U.toScheme))
  obtain ⟨u, huU, huc⟩ := nonempty_inter_closedPoints (Z := (U : Set G)) ⟨u₀.1, u₀.2⟩
    U.isOpen.isLocallyClosed
  rw [mem_closedPoints_iff] at huc
  let pz : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f := ⟨pointOfClosedPoint f z hzc,
    pointOfClosedPoint_comp f z hzc⟩
  let pu : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f := ⟨pointOfClosedPoint f u huc,
    pointOfClosedPoint_comp f u huc⟩
  let a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f := L.mul (𝟙 _) (L.inv (𝟙 _) pz) pu
  have hW := sat_preimage L i a U hU
  have hzW : z ∈ rt L a ⁻¹ᵁ U := by
    change (rt L a).base z ∈ U
    have h1 : (pz.1 ≫ rt L a) = (L.mul (𝟙 _) pz (const a (𝟙 _))).1 := comp_rt L a (𝟙 _) pz
    have h2 : const a (𝟙 (Spec (CommRingCat.of k))) = a := Subtype.ext (Category.id_comp _)
    rw [h2, show L.mul (𝟙 _) pz a = pu by rw [← L.mul_assoc, L.mul_inv_cancel, L.one_mul]] at h1
    have hz : pz.1 (show Spec (CommRingCat.of k) from IsLocalRing.closedPoint k) = z :=
      pointOfClosedPoint_apply f z hzc _
    have hu : pu.1 (show Spec (CommRingCat.of k) from IsLocalRing.closedPoint k) = u :=
      pointOfClosedPoint_apply f u huc _
    have he := congrArg (fun b : Spec (CommRingCat.of k) ⟶ G =>
      b (show Spec (CommRingCat.of k) from IsLocalRing.closedPoint k)) h1
    have he' : rt L a z = u := (congrArg (rt L a) hz).symm.trans (he.trans hu)
    exact he'.symm ▸ huU
  have hxW : x ∈ rt L a ⁻¹ᵁ U := (specializes_iff_mem_closure.mpr hzcl).mem_open (rt L a ⁻¹ᵁ
    U).isOpen hzW
  obtain ⟨Y, p, hco, hfl, hlfp, hqc, hsj, hpb⟩ := hloc
  have : Flat _ := hfl
  have : LocallyOfFinitePresentation _ := hlfp
  have : QuasiCompact _ := hqc
  have : Surjective _ := hsj
  exact ⟨rt L a ⁻¹ᵁ U, hW, hxW, Y, (rt L a ∣_ U) ≫ p, transport L i a U hU hW p hco hpb⟩

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_fppf_quotient_of_sliceQuotient.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.QuotientSliceDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace SliceDescent

section Points

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L :
    RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f)) {S : Scheme.{u}} (j : S ⟶ G)

/-- The action map restricted to the chosen transverse slice. -/
abbrev amap : pullback (i ≫ f) (j ≫ f) ⟶ G :=
  open AbelianVarieties.NOSProofs in
  FiniteSliceLocus.FiniteLocus.amap L i j

theorem mul_coe_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of k)} (h : t = t')
    (x y : SchemeHomOver t f) (x' y' : SchemeHomOver t' f) (hx : x.1 = x'.1) (hy : y.1 = y'.1) :
    (L.mul t x y).1 = (L.mul t' x' y').1 :=
  open AbelianVarieties.NOSProofs in
  FiniteSliceLocus.FiniteLocus.mul_coe_congr L h x y x' y' hx hy

/-- The subgroup point viewed in the ambient group. -/
def ipt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (n : SchemeHomOver t (i ≫ f)) :
    SchemeHomOver t f :=
  open AbelianVarieties.NOSProofs in
  FiniteSliceLocus.FiniteLocus.ipt i n

@[scoped simp] theorem ipt_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (n : SchemeHomOver
    t (i ≫ f)) :
    (ipt i n).1 = n.1 ≫ i :=
  open AbelianVarieties.NOSProofs in
  FiniteSliceLocus.FiniteLocus.ipt_coe i n

theorem ipt_eq_comp {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (n : SchemeHomOver t (i ≫ f))
    :
    ipt i n = NeronModelInfra.schemeHomOverComp n (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) :=
  open AbelianVarieties.NOSProofs in
  FiniteSliceLocus.FiniteLocus.ipt_eq_comp i n

/-- A subgroup point paired with a point of the slice. -/
def pairNS {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (n : SchemeHomOver t (i ≫ f)) (s : T ⟶
    S)
    (hs : s ≫ j ≫ f = t) : T ⟶ pullback (i ≫ f) (j ≫ f) :=
  open AbelianVarieties.NOSProofs in
  FiniteSliceLocus.FiniteLocus.pairNS i j n s hs

@[scoped simp] theorem pairNS_fst {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (n :
    SchemeHomOver t (i ≫ f))
    (s : T ⟶ S) (hs : s ≫ j ≫ f = t) : pairNS i j n s hs ≫ pullback.fst _ _ = n.1 :=
  open AbelianVarieties.NOSProofs in
  FiniteSliceLocus.FiniteLocus.pairNS_fst i j n s hs

@[scoped simp] theorem pairNS_snd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (n :
    SchemeHomOver t (i ≫ f))
    (s : T ⟶ S) (hs : s ≫ j ≫ f = t) : pairNS i j n s hs ≫ pullback.snd _ _ = s :=
  open AbelianVarieties.NOSProofs in
  FiniteSliceLocus.FiniteLocus.pairNS_snd i j n s hs

theorem comp_amap {T : Scheme.{u}} (z : T ⟶ pullback (i ≫ f) (j ≫ f)) (t : T ⟶ Spec (CommRingCat.of
    k))
    (ht : z ≫ pullback.fst _ _ ≫ i ≫ f = t) :
    z ≫ amap L i j =
      (L.mul t (ipt i ⟨z ≫ pullback.fst _ _, ht⟩)
        ⟨z ≫ pullback.snd _ _ ≫ j, by
          rw [Category.assoc, Category.assoc, ← pullback.condition]; exact ht⟩).1 :=
  open AbelianVarieties.NOSProofs in
  FiniteSliceLocus.FiniteLocus.comp_amap L i j z t ht

theorem pairNS_amap {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (n : SchemeHomOver t (i ≫ f))
    (s : T ⟶ S) (hs : s ≫ j ≫ f = t) :
    pairNS i j n s hs ≫ amap L i j = (L.mul t (ipt i n) ⟨s ≫ j, hs⟩).1 :=
  open AbelianVarieties.NOSProofs in
  FiniteSliceLocus.FiniteLocus.pairNS_amap L i j n s hs

theorem ipt_mul
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)) :
    ipt i (LN.mul t x y) = L.mul t (ipt i x) (ipt i y) :=
  open AbelianVarieties.NOSProofs in
  FiniteSliceLocus.FiniteLocus.ipt_mul L i LN hi t x y

theorem ipt_injective [IsClosedImmersion i] {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (x y : SchemeHomOver t (i ≫ f)) (h : ipt i x = ipt i y) : x = y :=
  open AbelianVarieties.NOSProofs in
  FiniteSliceLocus.FiniteLocus.ipt_injective i x y h

end Points

section Action

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L :
    RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f)) {S : Scheme.{u}} (j : S ⟶ G)

theorem comp_action {T : Scheme.{u}} (α : T ⟶ pullback (i ≫ f) f) (t : T ⟶ Spec (CommRingCat.of k))
    (ht : α ≫ pullback.fst _ _ ≫ i ≫ f = t) :
    α ≫ L.action i =
      (L.mul t (ipt i ⟨α ≫ pullback.fst _ _, ht⟩)
        ⟨α ≫ pullback.snd _ _, by rw [Category.assoc, ← pullback.condition]; exact ht⟩).1 :=
  open AbelianVarieties.NOSProofs in
  SliceEquivalence.SliceRelation.comp_action L i α t ht

variable (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))

include hi in
theorem ipt_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) : ipt i (LN.one t) = L.one t
    :=
  open AbelianVarieties.NOSProofs in
  FiniteSliceLocus.FiniteLocus.ipt_one L i LN hi t

include hi in
theorem ipt_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (m : SchemeHomOver t (i ≫ f)) :
    ipt i (LN.inv t m) = L.inv t (ipt i m) :=
  open AbelianVarieties.NOSProofs in
  FiniteSliceLocus.FiniteLocus.ipt_inv L i LN hi t m

include hi in
theorem pairNS_mul_amap {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (m n : SchemeHomOver t (i
    ≫ f))
    (s : T ⟶ S) (hs : s ≫ j ≫ f = t) :
    pairNS i j (LN.mul t m n) s hs ≫ amap L i j =
      (L.mul t (ipt i m) ⟨pairNS i j n s hs ≫ amap L i j, by
        rw [pairNS_amap]; exact (L.mul t _ _).2⟩).1 :=
  open AbelianVarieties.NOSProofs in
  SliceEquivalence.SliceRelation.pairNS_mul_amap L i LN j hi m n s hs

omit hi in
theorem amap_over : amap L i j ≫ f = pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f :=
  open AbelianVarieties.NOSProofs in
  FiniteSliceLocus.FiniteLocus.amap_over L i j

omit hi in
theorem eq_pairNS {T : Scheme.{u}} (z : T ⟶ pullback (i ≫ f) (j ≫ f)) (t : T ⟶ Spec (CommRingCat.of
    k))
    (ht : z ≫ pullback.fst _ _ ≫ i ≫ f = t) :
    z = pairNS i j ⟨z ≫ pullback.fst _ _, ht⟩ (z ≫ pullback.snd _ _)
      (by rw [Category.assoc, ← pullback.condition]; exact ht) :=
  open AbelianVarieties.NOSProofs in
  SliceEquivalence.SliceRelation.eq_pairNS i j z t ht

include LN hi in
theorem action_mem_image_of_snd_mem_image (V : Set ↥S) (x : ↥(pullback (i ≫ f) f))
    (hx : (pullback.snd (i ≫ f) f).base x ∈
      (amap L i j).base '' ((pullback.snd (i ≫ f) (j ≫ f)).base ⁻¹' V)) :
    (L.action i).base x ∈ (amap L i j).base '' ((pullback.snd (i ≫ f) (j ≫ f)).base ⁻¹' V) := by
  obtain ⟨y, hyV, hxy⟩ := hx
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd (i ≫ f) f)
    (g := amap L i j) x y hxy.symm
  let Q := pullback (pullback.snd (i ≫ f) f) (amap L i j)
  let t : Q ⟶ Spec (CommRingCat.of k) := pullback.snd _ _ ≫ pullback.fst _ _ ≫ i ≫ f
  have hm : (pullback.fst _ _ ≫ pullback.fst (i ≫ f) f) ≫ i ≫ f = t := by
    change (pullback.fst _ _ ≫ pullback.fst (i ≫ f) f) ≫ i ≫ f =
      pullback.snd (pullback.snd (i ≫ f) f) (amap L i j) ≫ pullback.fst _ _ ≫ i ≫ f
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
      amap_over,
      ← pullback.condition]
  let m : SchemeHomOver t (i ≫ f) := ⟨pullback.fst _ _ ≫ pullback.fst (i ≫ f) f, hm⟩
  let n : SchemeHomOver t (i ≫ f) := ⟨pullback.snd _ _ ≫ pullback.fst (i ≫ f) (j ≫ f),
    Category.assoc _ _ _⟩
  have hs : (pullback.snd (pullback.snd (i ≫ f) f) (amap L i j) ≫ pullback.snd (i ≫ f) (j ≫ f)) ≫ j
    ≫ f = t := by
    change _ = pullback.snd (pullback.snd (i ≫ f) f) (amap L i j) ≫ pullback.fst _ _ ≫ i ≫ f
    rw [Category.assoc, ← pullback.condition]
  let μ : Q ⟶ pullback (i ≫ f) (j ≫ f) := pairNS i j (LN.mul t m n) _ hs
  have hμ : μ ≫ amap L i j = pullback.fst _ _ ≫ L.action i := by
    rw [pairNS_mul_amap L i LN j hi,
      comp_action L i (pullback.fst (pullback.snd (i ≫ f) f) (amap L i j)) t (by
          simpa only [Category.assoc] using hm)]
    apply mul_coe_congr L rfl _ _ _ _ rfl
    change pairNS i j n _ hs ≫ amap L i j = pullback.fst _ _ ≫ pullback.snd (i ≫ f) f
    rw [← eq_pairNS i j (pullback.snd _ _) t rfl, pullback.condition]
  refine ⟨μ.base z, ?_, ?_⟩
  · change (μ ≫ pullback.snd (i ≫ f) (j ≫ f)).base z ∈ V
    rw [pairNS_snd]
    change (pullback.snd (i ≫ f) (j ≫ f)).base ((pullback.snd (pullback.snd (i ≫ f) f) (amap L i
      j)).base z) ∈ V
    rw [hz2]; exact hyV
  · change (μ ≫ amap L i j).base z = _
    rw [hμ, ← hz1]; rfl

include LN hi in
theorem snd_mem_image_of_action_mem_image (V : Set ↥S) (x : ↥(pullback (i ≫ f) f))
    (hx : (L.action i).base x ∈ (amap L i j).base '' ((pullback.snd (i ≫ f) (j ≫ f)).base ⁻¹' V)) :
    (pullback.snd (i ≫ f) f).base x ∈ (amap L i j).base '' ((pullback.snd (i ≫ f) (j ≫ f)).base ⁻¹'
      V) := by
  obtain ⟨y, hyV, hxy⟩ := hx
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := L.action i)
    (g := amap L i j) x y hxy.symm
  let Q := pullback (L.action i) (amap L i j)
  let t : Q ⟶ Spec (CommRingCat.of k) := pullback.snd _ _ ≫ pullback.fst _ _ ≫ i ≫ f
  have hm : (pullback.fst _ _ ≫ pullback.fst (i ≫ f) f) ≫ i ≫ f = t := by
    change (pullback.fst _ _ ≫ pullback.fst (i ≫ f) f) ≫ i ≫ f =
      pullback.snd (L.action i) (amap L i j) ≫ pullback.fst _ _ ≫ i ≫ f
    rw [Category.assoc, pullback.condition,
      show pullback.snd (i ≫ f) f ≫ f = L.action i ≫ f from (RelativeGroupLaw.action_over L i).symm,
      ← Category.assoc, pullback.condition, Category.assoc, amap_over, ← pullback.condition]
  let m : SchemeHomOver t (i ≫ f) := ⟨pullback.fst _ _ ≫ pullback.fst (i ≫ f) f, hm⟩
  let n : SchemeHomOver t (i ≫ f) := ⟨pullback.snd _ _ ≫ pullback.fst (i ≫ f) (j ≫ f),
    Category.assoc _ _ _⟩
  have hs : (pullback.snd (L.action i) (amap L i j) ≫ pullback.snd (i ≫ f) (j ≫ f)) ≫ j ≫ f = t
    := by
    change _ = pullback.snd (L.action i) (amap L i j) ≫ pullback.fst _ _ ≫ i ≫ f
    rw [Category.assoc, ← pullback.condition]
  let μ : Q ⟶ pullback (i ≫ f) (j ≫ f) := pairNS i j (LN.mul t (LN.inv t m) n) _ hs
  have hμ : μ ≫ amap L i j = pullback.fst _ _ ≫ pullback.snd (i ≫ f) f := by
    rw [pairNS_mul_amap L i LN j hi, ipt_inv L i LN hi]
    have hn : pairNS i j n _ hs ≫ amap L i j = pullback.fst _ _ ≫ L.action i := by
      rw [← eq_pairNS i j (pullback.snd _ _) t rfl, pullback.condition]
    have hact := comp_action L i (pullback.fst (L.action i) (amap L i j)) t (by
        simpa only [Category.assoc] using hm)
    let : Group (SchemeHomOver t f) := L.pointGroup t
    have key : L.mul t (L.inv t (ipt i m)) ⟨pairNS i j n _ hs ≫ amap L i j, by
        rw [pairNS_amap]; exact (L.mul t _ _).2⟩ =
        ⟨pullback.fst _ _ ≫ pullback.snd (i ≫ f) f, by
          rw [Category.assoc, ← pullback.condition, ← Category.assoc]; exact hm⟩ := by
      have e1 : (⟨pairNS i j n _ hs ≫ amap L i j, by rw [pairNS_amap]; exact (L.mul t _ _).2⟩ :
        SchemeHomOver t f) =
          L.mul t (ipt i m) ⟨pullback.fst _ _ ≫ pullback.snd (i ≫ f) f, by
            rw [Category.assoc, ← pullback.condition, ← Category.assoc]; exact hm⟩ := by
        apply Subtype.ext; exact hn.trans hact
      rw [e1]
      change (ipt i m)⁻¹ * (ipt i m * _) = _
      rw [inv_mul_cancel_left]
    exact congrArg Subtype.val key
  refine ⟨μ.base z, ?_, ?_⟩
  · change (μ ≫ pullback.snd (i ≫ f) (j ≫ f)).base z ∈ V
    rw [pairNS_snd]
    change (pullback.snd (i ≫ f) (j ≫ f)).base ((pullback.snd (L.action i) (amap L i j)).base z) ∈ V
    rw [hz2]; exact hyV
  · change (μ ≫ amap L i j).base z = _
    rw [hμ, ← hz1]; rfl

end Action

section Descent

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L :
    RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f))
  (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
  {S : Scheme.{u}} (j : S ⟶ G) (V : S.Opens)

/-- The inverse image of the slice neighborhood. -/
abbrev NV : (pullback (i ≫ f) (j ≫ f)).Opens := pullback.snd (i ≫ f) (j ≫ f) ⁻¹ᵁ V

/-- The open image of the action on the slice neighborhood. -/
def Uimg [UniversallyOpen (amap L i j)] : G.Opens :=
  (amap L i j).isOpenMap.functor.obj (NV (f := f) i j V)

theorem coe_Uimg [UniversallyOpen (amap L i j)] :
    (Uimg L i j V : Set ↥G) = (amap L i j).base '' ((pullback.snd (i ≫ f) (j ≫ f)).base ⁻¹' (V : Set
      ↥S)) := rfl

theorem le_preimage_Uimg [UniversallyOpen (amap L i j)] : NV (f := f) i j V ≤ amap L i j ⁻¹ᵁ Uimg L
    i j V :=
  fun _x hx => Set.mem_image_of_mem _ hx

/-- The action map onto its open image. -/
def cover [UniversallyOpen (amap L i j)] : (NV (f := f) i j V).toScheme ⟶ (Uimg L i j V).toScheme :=
  (amap L i j).resLE (Uimg L i j V) (NV (f := f) i j V) (le_preimage_Uimg L i j V)

theorem cover_ι [UniversallyOpen (amap L i j)] :
    cover L i j V ≫ (Uimg L i j V).ι = (NV (f := f) i j V).ι ≫ amap L i j := Scheme.Hom.resLE_comp_ι
      _ _

scoped instance cover_surjective [UniversallyOpen (amap L i j)] : Surjective (cover L i j V) := by
  refine ⟨fun u => ?_⟩
  obtain ⟨y0, hy0, hu⟩ := u.2
  have : y0 ∈ Set.range (NV (f := f) i j V).ι.base := by rw [Scheme.Opens.range_ι]; exact hy0
  obtain ⟨y, rfl⟩ := this
  refine ⟨y, ?_⟩
  apply (Uimg L i j V).ι.isOpenEmbedding.injective
  change ((cover L i j V) ≫ (Uimg L i j V).ι).base y = _
  rw [cover_ι]
  exact hu

scoped instance cover_flat [UniversallyOpen (amap L i j)] [Flat (amap L i j)] : Flat (cover L i j V)
    := by
  unfold cover; infer_instance

scoped instance cover_lfp [UniversallyOpen (amap L i j)] [LocallyOfFinitePresentation (amap L i j)]
    :
    LocallyOfFinitePresentation (cover L i j V) := by
  unfold cover; infer_instance

include LN hi in
theorem Uimg_saturated [IsClosedImmersion i] [UniversallyOpen (amap L i j)] :
    pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V = L.action i ⁻¹ᵁ Uimg L i j V := by
  apply le_antisymm
  · intro x hx
    exact action_mem_image_of_snd_mem_image L i LN j hi (V : Set ↥S) x hx
  · intro x hx
    exact snd_mem_image_of_action_mem_image L i LN j hi (V : Set ↥S) x hx

include LN in
theorem surjective_if : Surjective (i ≫ f) := by
  refine ⟨fun s => ⟨(LN.one (𝟙 _)).1.base s, ?_⟩⟩
  change ((LN.one (𝟙 _)).1 ≫ i ≫ f).base s = s
  rw [(LN.one (𝟙 _)).2]; rfl

include LN in
theorem nonempty_Uimg [UniversallyOpen (amap L i j)] [Nonempty V.toScheme] : Nonempty (Uimg L i j
    V).toScheme := by
  obtain ⟨v⟩ := (inferInstance : Nonempty V.toScheme)
  have : Surjective (i ≫ f) := surjective_if i LN
  obtain ⟨y, hy⟩ := (pullback.snd (i ≫ f) (j ≫ f)).surjective (V.ι.base v)
  have hyV : y ∈ NV (f := f) i j V := by
    change (pullback.snd (i ≫ f) (j ≫ f)).base y ∈ (V : Set ↥S)
    rw [hy, ← Scheme.Opens.range_ι V]; exact ⟨v, rfl⟩
  exact ⟨⟨(amap L i j).base y, Set.mem_image_of_mem _ hyV⟩⟩

end Descent

section KernelPair

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L :
    RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f))
  (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
  {S : Scheme.{u}} (j : S ⟶ G) (V : S.Opens)

/-- The first projection of the slice relation. -/
abbrev q₁ : pullback (amap L i j) j ⟶ S := pullback.fst (amap L i j) j ≫ pullback.snd (i ≫ f) (j ≫
    f)
/-- The second projection of the slice relation. -/
abbrev q₂ : pullback (amap L i j) j ⟶ S := pullback.snd (amap L i j) j

omit hi in
theorem amap_over' : amap L i j ≫ f = pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫ f := by
  rw [amap_over, pullback.condition]

include LN hi in
theorem kernel_pair [IsClosedImmersion i] [UniversallyOpen (amap L i j)]
    (hV : q₁ L i j ⁻¹ᵁ V = q₂ L i j ⁻¹ᵁ V) {Y : Scheme.{u}} (π : V.toScheme ⟶ Y)
    (w : (q₁ L i j ∣_ V) ≫ π = (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)) ≫ π)
    {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ (NV (f := f) i j V).toScheme)
    (h : g₁ ≫ cover L i j V = g₂ ≫ cover L i j V) :
    g₁ ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) ≫ π = g₂ ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) ≫ π
      := by
  have hz : (g₁ ≫ (NV (f := f) i j V).ι) ≫ amap L i j = (g₂ ≫ (NV (f := f) i j V).ι) ≫ amap L i j
    := by
    rw [Category.assoc, Category.assoc, ← cover_ι, ← Category.assoc, h, Category.assoc]
  have ht₁ : (g₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _ ≫ i ≫ f =
      (g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _ ≫ i ≫ f := by
    rw [← amap_over', ← Category.assoc, hz, Category.assoc]
  obtain ⟨t, hzt₂⟩ : ∃ t : Z ⟶ Spec (CommRingCat.of k),
      (g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _ ≫ i ≫ f = t := ⟨_, rfl⟩
  have hzt₁ : (g₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _ ≫ i ≫ f = t := ht₁.trans hzt₂
  let n₁ : SchemeHomOver t (i ≫ f) := ⟨(g₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _, by
      simpa only [Category.assoc] using hzt₁⟩
  let n₂ : SchemeHomOver t (i ≫ f) := ⟨(g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _, by
      simpa only [Category.assoc] using hzt₂⟩
  have hs₁ : ((g₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _) ≫ j ≫ f = t := by
    rw [Category.assoc, ← pullback.condition]; exact hzt₁
  have hs₂ : ((g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _) ≫ j ≫ f = t := by
    rw [Category.assoc, ← pullback.condition]; exact hzt₂
  have key : L.mul t (ipt i n₁) ⟨((g₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _) ≫ j, by
      simpa only [Category.assoc] using hs₁⟩ =
      L.mul t (ipt i n₂) ⟨((g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _) ≫ j, by
          simpa only [Category.assoc] using hs₂⟩ := by
    apply Subtype.ext
    have e₁ := comp_amap L i j (g₁ ≫ (NV (f := f) i j V).ι) t hzt₁
    have e₂ := comp_amap L i j (g₂ ≫ (NV (f := f) i j V).ι) t hzt₂
    rw [hz] at e₁
    rw [e₁] at e₂
    refine (mul_coe_congr L rfl _ _ _ _ ?_ ?_).trans (e₂.trans (mul_coe_congr L rfl _ _ _ _ ?_ ?_))
    · change ((g₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _) ≫ i = _
      simp only [ipt_coe, Category.assoc]
    · change (((g₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _) ≫ j) = _
      simp only [Category.assoc]
    · change _ = ((g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _) ≫ i
      simp only [ipt_coe, Category.assoc]
    · change _ = (((g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _) ≫ j)
      simp only [Category.assoc]
  let r : Z ⟶ pullback (i ≫ f) (j ≫ f) := pairNS i j (LN.mul t (LN.inv t n₂) n₁) _ hs₁
  have hr : r ≫ amap L i j = ((g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _) ≫ j := by
    change pairNS i j (LN.mul t (LN.inv t n₂) n₁) _ hs₁ ≫ amap L i j = _
    rw [pairNS_mul_amap L i LN j hi, ipt_inv L i LN hi]
    let : Group (SchemeHomOver t f) := L.pointGroup t
    have e1 : (⟨pairNS i j n₁ _ hs₁ ≫ amap L i j, by rw [pairNS_amap]; exact (L.mul t _ _).2⟩ :
      SchemeHomOver t f) =
        L.mul t (ipt i n₂) ⟨((g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _) ≫ j, by
            simpa only [Category.assoc] using hs₂⟩ := by
      rw [← key]; apply Subtype.ext; exact pairNS_amap L i j n₁ _ hs₁
    have e2 : L.mul t (L.inv t (ipt i n₂)) ⟨pairNS i j n₁ _ hs₁ ≫ amap L i j, by
        rw [pairNS_amap]
        exact (L.mul t _ _).2⟩ =
        ⟨((g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _) ≫ j, by
            simpa only [Category.assoc] using hs₂⟩
          := by
      rw [e1]
      change (ipt i n₂)⁻¹ * (ipt i n₂ * _) = _
      rw [inv_mul_cancel_left]
    exact congrArg Subtype.val e2
  let ρ : Z ⟶ pullback (amap L i j) j := pullback.lift r _ hr
  have hρ₁ : ρ ≫ q₁ L i j = (g₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _ := by
    change ρ ≫ pullback.fst _ _ ≫ pullback.snd _ _ = _
    rw [← Category.assoc, pullback.lift_fst]
    exact pairNS_snd i j _ _ hs₁
  have hρ₂ : ρ ≫ q₂ L i j = (g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _ := pullback.lift_snd _ _
    _
  have hρV : Set.range ρ.base ⊆ Set.range (q₁ L i j ⁻¹ᵁ V).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change (ρ ≫ q₁ L i j).base z ∈ (V : Set ↥S)
    rw [hρ₁]
    change (pullback.snd (i ≫ f) (j ≫ f)).base ((NV (f := f) i j V).ι.base (g₁.base z)) ∈ (V : Set
      ↥S)
    have : (NV (f := f) i j V).ι.base (g₁.base z) ∈ NV (f := f) i j V := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨_, rfl⟩
    exact this
  let ρ' : Z ⟶ (q₁ L i j ⁻¹ᵁ V).toScheme := IsOpenImmersion.lift (q₁ L i j ⁻¹ᵁ V).ι ρ hρV
  have hρ' : ρ' ≫ (q₁ L i j ⁻¹ᵁ V).ι = ρ := IsOpenImmersion.lift_fac _ _ _
  have A : ρ' ≫ (q₁ L i j ∣_ V) = g₁ ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hρ', hρ₁,
      Category.assoc,
      Category.assoc, morphismRestrict_ι]
  have B : ρ' ≫ ((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V) =
      g₂ ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) := by
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι, ← Category.assoc
      (Iso.hom _),
      Scheme.isoOfEq_hom_ι, ← Category.assoc, hρ', hρ₂, Category.assoc, Category.assoc,
        morphismRestrict_ι]
  calc g₁ ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) ≫ π = ρ' ≫ (q₁ L i j ∣_ V) ≫ π := by
        rw [← Category.assoc, ← A, Category.assoc]
    _ = ρ' ≫ (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)) ≫ π := by rw [w]
    _ = g₂ ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) ≫ π := by
        rw [← Category.assoc, B, Category.assoc]

end KernelPair

section Generic

theorem quasiCompact_of_comp_surjective {X U Y : Scheme.{u}} (c : X ⟶ U) [Surjective c] (p : U ⟶ Y)
    [QuasiCompact (c ≫ p)] : QuasiCompact p := by
  refine ⟨fun W hW hWc => ?_⟩
  have h := QuasiCompact.isCompact_preimage (f := c ≫ p) W hW hWc
  have : p.base ⁻¹' W = c.base '' ((c ≫ p).base ⁻¹' W) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_of_subset]
    rw [Set.range_eq_univ.mpr c.surjective]; exact Set.subset_univ _
  rw [this]
  exact h.image c.continuous

end Generic

section Quotient

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L :
    RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
  (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
  {S : Scheme.{u}} (j : S ⟶ G) (V : S.Opens)
  [UniversallyOpen (amap L i j)] [Flat (amap L i j)] [LocallyOfFinitePresentation (amap L i j)]
  (hV : q₁ L i j ⁻¹ᵁ V = q₂ L i j ⁻¹ᵁ V) {Y : Scheme.{u}} (π : V.toScheme ⟶ Y)
  (w : (q₁ L i j ∣_ V) ≫ π = (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)) ≫ π)

/-- The descended map from the saturated open chart. -/
def pdesc : (Uimg L i j V).toScheme ⟶ Y :=
  EffectiveEpi.desc (cover L i j V) ((pullback.snd (i ≫ f) (j ≫ f) ∣_ V) ≫ π)
    (fun g₁ g₂ h => kernel_pair L i LN hi j V hV π w g₁ g₂ h)

theorem cover_pdesc : cover L i j V ≫ pdesc L i LN hi j V hV π w = (pullback.snd (i ≫ f) (j ≫ f) ∣_
    V) ≫ π :=
  EffectiveEpi.fac (cover L i j V) _ (fun g₁ g₂ h => kernel_pair L i LN hi j V hV π w g₁ g₂ h)

include LN in
theorem surjective_pdesc [Surjective π] : Surjective (pdesc L i LN hi j V hV π w) := by
  have : Surjective (i ≫ f) := surjective_if i LN
  have : Surjective (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) :=
    IsZariskiLocalAtTarget.restrict
      (P := (@Surjective : MorphismProperty Scheme.{u})) inferInstance V
  have : Surjective (cover L i j V ≫ pdesc L i LN hi j V hV π w) := by
    rw [cover_pdesc]
    infer_instance
  exact Surjective.of_comp (cover L i j V) _

theorem flat_pdesc [Flat (i ≫ f)] [Flat π] : Flat (pdesc L i LN hi j V hV π w) := by
  have : Flat (cover L i j V ≫ pdesc L i LN hi j V hV π w) := by rw [cover_pdesc]; infer_instance
  exact AlgebraicGeometry.Flat.of_comp_of_flat_of_surjective (cover L i j V) _

theorem quasiCompact_pdesc [QuasiCompact (i ≫ f)] [QuasiCompact π] : QuasiCompact (pdesc L i LN hi j
    V hV π w) := by
  have : QuasiCompact (cover L i j V ≫ pdesc L i LN hi j V hV π w) := by
    rw [cover_pdesc]
    infer_instance
  exact quasiCompact_of_comp_surjective (cover L i j V) _

/-- The structural map descended from the slice quotient. -/
def yK (hcoeq : IsColimit (Cofork.ofπ π w)) : Y ⟶ Spec (CommRingCat.of k) :=
  (Cofork.IsColimit.desc' hcoeq (V.ι ≫ j ≫ f) (by
    have e : pullback.fst (amap L i j) j ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f = pullback.snd (amap
      L i j) j ≫ j ≫ f := by
      rw [← amap_over, ← Category.assoc, pullback.condition, Category.assoc]
    have h1 : (q₁ L i j ∣_ V) ≫ V.ι ≫ j ≫ f = (q₁ L i j ⁻¹ᵁ V).ι ≫ pullback.snd (amap L i j) j ≫ j ≫
      f := by
      rw [← Category.assoc, morphismRestrict_ι]
      simp only [Category.assoc]
      rw [e]
    have h2 : (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)) ≫ V.ι ≫ j ≫ f =
        (q₁ L i j ⁻¹ᵁ V).ι ≫ pullback.snd (amap L i j) j ≫ j ≫ f := by
      have h3 : ((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V) ≫ V.ι = (q₁ L i j ⁻¹ᵁ
        V).ι ≫ q₂ L i j := by
        rw [morphismRestrict_ι, ← Category.assoc, Scheme.isoOfEq_hom_ι]
      rw [Category.assoc, ← Category.assoc (q₂ L i j ∣_ V), ← Category.assoc ((pullback (amap L i j)
        j).isoOfEq hV).hom, h3,
        Category.assoc]
    rw [h1, h2])).1

omit [IsClosedImmersion i] [UniversallyOpen (amap L i j)]
  [Flat (amap L i j)] [LocallyOfFinitePresentation (amap L i j)] in
theorem π_yK (hcoeq : IsColimit (Cofork.ofπ π w)) : π ≫ yK L i j V hV π w hcoeq = V.ι ≫ j ≫ f :=
  (Cofork.IsColimit.desc' hcoeq (V.ι ≫ j ≫ f) _).2

theorem pdesc_yK (hcoeq : IsColimit (Cofork.ofπ π w)) :
    pdesc L i LN hi j V hV π w ≫ yK L i j V hV π w hcoeq = (Uimg L i j V).ι ≫ f := by
  rw [← cancel_epi (cover L i j V), ← Category.assoc, cover_pdesc, Category.assoc, π_yK, ←
    Category.assoc,
    morphismRestrict_ι, Category.assoc, ← amap_over, ← Category.assoc, ← cover_ι L i j V,
      Category.assoc]

omit [IsClosedImmersion i] in
theorem isLocallyNoetherian_Y [IsAffine S] [LocallyOfFiniteType (j ≫ f)] [Flat π] [Surjective π]
    [QuasiCompact π] :
    IsLocallyNoetherian Y := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (j ≫ f)
  exact AlgebraicGeometry.isLocallyNoetherian_of_flat_of_surjective_of_quasiCompact π

theorem locallyOfFinitePresentation_pdesc (hcoeq : IsColimit (Cofork.ofπ π w)) [LocallyOfFiniteType
    f]
    [IsAffine S] [LocallyOfFiniteType (j ≫ f)] [Flat π] [Surjective π] [QuasiCompact π] :
    LocallyOfFinitePresentation (pdesc L i LN hi j V hV π w) := by
  have : LocallyOfFiniteType (pdesc L i LN hi j V hV π w ≫ yK L i j V hV π w hcoeq) := by
    rw [pdesc_yK]; infer_instance
  have : LocallyOfFiniteType (pdesc L i LN hi j V hV π w) := locallyOfFiniteType_of_comp _ (yK L i j
    V hV π w hcoeq)
  have : IsLocallyNoetherian Y := isLocallyNoetherian_Y (f := f) j V π
  exact AlgebraicGeometry.locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian
    (pdesc L i LN hi j V hV π w) (𝟙 Y) (pdesc L i LN hi j V hV π w) (Category.comp_id _)

end Quotient

section Square

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L :
    RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
  (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
  {S : Scheme.{u}} (j : S ⟶ G) (V : S.Opens)

include hi in
omit [IsClosedImmersion i] in
theorem exists_translate {Q : Scheme.{u}} (α : Q ⟶ pullback (i ≫ f) f)
    (β : Q ⟶ (NV (f := f) i j V).toScheme)
    (hαβ : α ≫ pullback.snd (i ≫ f) f = β ≫ (NV (f := f) i j V).ι ≫ amap L i j) :
    ∃ μ : Q ⟶ (NV (f := f) i j V).toScheme,
      μ ≫ (NV (f := f) i j V).ι ≫ amap L i j = α ≫ L.action i ∧
      μ ≫ (NV (f := f) i j V).ι ≫ pullback.snd (i ≫ f) (j ≫ f) =
        β ≫ (NV (f := f) i j V).ι ≫ pullback.snd (i ≫ f) (j ≫ f) := by
  obtain ⟨t, ht⟩ : ∃ t : Q ⟶ Spec (CommRingCat.of k),
      (β ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _ ≫ i ≫ f = t := ⟨_, rfl⟩
  have hm : (α ≫ pullback.fst (i ≫ f) f) ≫ i ≫ f = t := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hαβ, Category.assoc, Category.assoc,
      amap_over',
      ← Category.assoc]
    exact ht
  let m : SchemeHomOver t (i ≫ f) := ⟨α ≫ pullback.fst (i ≫ f) f, hm⟩
  let n : SchemeHomOver t (i ≫ f) := ⟨(β ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _, by
      simpa only [Category.assoc] using ht⟩
  have hs : ((β ≫ (NV (f := f) i j V).ι) ≫ pullback.snd (i ≫ f) (j ≫ f)) ≫ j ≫ f = t := by
    rw [Category.assoc, ← pullback.condition]; exact ht
  let μ₀ : Q ⟶ pullback (i ≫ f) (j ≫ f) := pairNS i j (LN.mul t m n) _ hs
  have hμ₀ : μ₀ ≫ amap L i j = α ≫ L.action i := by
    change pairNS i j (LN.mul t m n) _ hs ≫ amap L i j = _
    rw [pairNS_mul_amap L i LN j hi, comp_action L i α t (by simpa only [Category.assoc] using hm)]
    apply mul_coe_congr L rfl _ _ _ _ rfl
    change pairNS i j n _ hs ≫ amap L i j = α ≫ pullback.snd (i ≫ f) f
    rw [← eq_pairNS i j (β ≫ (NV (f := f) i j V).ι) t ht, Category.assoc, hαβ]
  have hμ₀snd : μ₀ ≫ pullback.snd (i ≫ f) (j ≫ f) = (β ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _
    :=
    pairNS_snd i j _ _ hs
  have hrange : Set.range μ₀.base ⊆ Set.range (NV (f := f) i j V).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    change (μ₀ ≫ pullback.snd (i ≫ f) (j ≫ f)).base q ∈ (V : Set ↥S)
    rw [hμ₀snd]
    change (pullback.snd (i ≫ f) (j ≫ f)).base ((NV (f := f) i j V).ι.base (β.base q)) ∈ (V : Set
      ↥S)
    have : (NV (f := f) i j V).ι.base (β.base q) ∈ NV (f := f) i j V := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨_, rfl⟩
    exact this
  refine ⟨IsOpenImmersion.lift (NV (f := f) i j V).ι μ₀ hrange, ?_, ?_⟩
  · rw [← Category.assoc, IsOpenImmersion.lift_fac, hμ₀]
  · rw [← Category.assoc, IsOpenImmersion.lift_fac, hμ₀snd, Category.assoc]

variable [UniversallyOpen (amap L i j)] [Flat (amap L i j)] [LocallyOfFinitePresentation (amap L i
    j)]
  (hV : q₁ L i j ⁻¹ᵁ V = q₂ L i j ⁻¹ᵁ V) {Y : Scheme.{u}} (π : V.toScheme ⟶ Y)
  (w : (q₁ L i j ∣_ V) ≫ π = (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)) ≫ π)

include LN hi in
theorem square (hU : pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V = L.action i ⁻¹ᵁ Uimg L i j V) :
    (pullback.snd (i ≫ f) f ∣_ Uimg L i j V) ≫ pdesc L i LN hi j V hV π w =
      (((pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ Uimg L i j V)) ≫ pdesc L i LN hi j V
        hV π w := by
  let P₁ := pullback.snd (i ≫ f) f ∣_ Uimg L i j V
  let ν := pullback.fst P₁ (cover L i j V)
  have : Epi ν := by
    have : EffectiveEpi ν := inferInstance
    infer_instance
  rw [← cancel_epi ν]
  have hαβ : (ν ≫ (pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V).ι) ≫ pullback.snd (i ≫ f) f =
      pullback.snd P₁ (cover L i j V) ≫ (NV (f := f) i j V).ι ≫ amap L i j := by
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, pullback.condition, Category.assoc,
      cover_ι]
  obtain ⟨μ, hμa, hμb⟩ := exists_translate L i LN hi j V (ν ≫ (pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j
    V).ι)
    (pullback.snd P₁ (cover L i j V)) hαβ
  have hμcover : μ ≫ cover L i j V = ν ≫ ((pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ Uimg
    L i j V) := by
    rw [← cancel_mono (Uimg L i j V).ι, Category.assoc, cover_ι, hμa]
    simp only [Category.assoc]
    rw [morphismRestrict_ι, ← Category.assoc (Iso.hom _), Scheme.isoOfEq_hom_ι]
  have hμsnd : μ ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) = pullback.snd P₁ (cover L i j V) ≫
    (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, Category.assoc, morphismRestrict_ι]
    exact hμb
  calc ν ≫ P₁ ≫ pdesc L i LN hi j V hV π w
      = (pullback.snd P₁ (cover L i j V) ≫ cover L i j V) ≫ pdesc L i LN hi j V hV π w := by
        rw [← Category.assoc, pullback.condition]
    _ = pullback.snd P₁ (cover L i j V) ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) ≫ π := by
        rw [Category.assoc, cover_pdesc]
    _ = μ ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) ≫ π := by rw [← Category.assoc, ← hμsnd,
      Category.assoc]
    _ = μ ≫ cover L i j V ≫ pdesc L i LN hi j V hV π w := by rw [cover_pdesc]
    _ = ν ≫ (((pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ Uimg L i j V)) ≫ pdesc L i LN hi
      j V hV π w := by
        rw [← Category.assoc, hμcover]; simp only [Category.assoc]

end Square

section Effective

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L :
    RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
  (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
  {S : Scheme.{u}} (j : S ⟶ G) (V : S.Opens)
  [UniversallyOpen (amap L i j)] [Flat (amap L i j)] [LocallyOfFinitePresentation (amap L i j)]

/-- The first projection of the restricted action relation. -/
abbrev P₁ : (pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V).toScheme ⟶ (Uimg L i j V).toScheme :=
  pullback.snd (i ≫ f) f ∣_ Uimg L i j V

/-- The action projection of the restricted relation. -/
abbrev P₂ (hU : pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V = L.action i ⁻¹ᵁ Uimg L i j V) :
    (pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V).toScheme ⟶ (Uimg L i j V).toScheme :=
  ((pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ Uimg L i j V)

omit [Flat (amap L i j)] [LocallyOfFinitePresentation (amap L i j)] in
omit [IsClosedImmersion i] in
theorem P₁_ι : P₁ L i j V ≫ (Uimg L i j V).ι = (pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V).ι ≫
    pullback.snd (i ≫ f) f :=
  morphismRestrict_ι _ _

omit [Flat (amap L i j)] [LocallyOfFinitePresentation (amap L i j)] in
omit [IsClosedImmersion i] in
theorem P₂_ι (hU : pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V = L.action i ⁻¹ᵁ Uimg L i j V) :
    P₂ L i j V hU ≫ (Uimg L i j V).ι = (pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V).ι ≫ L.action i
      := by
  change (((pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ Uimg L i j V)) ≫ (Uimg L i j V).ι =
    _
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.isoOfEq_hom_ι]

include hi in
omit [UniversallyOpen (amap L i j)] [Flat (amap L i j)] [LocallyOfFinitePresentation (amap L i j)]
  in
omit hi in
theorem eq_of_snd_eq_of_action_eq {T : Scheme.{u}} (a b : T ⟶ pullback (i ≫ f) f)
    (h₁ : a ≫ pullback.snd (i ≫ f) f = b ≫ pullback.snd (i ≫ f) f) (h₂ : a ≫ L.action i = b ≫
      L.action i) :
    a = b := by
  obtain ⟨t, hta⟩ : ∃ t : T ⟶ Spec (CommRingCat.of k), a ≫ pullback.fst (i ≫ f) f ≫ i ≫ f = t := ⟨_,
    rfl⟩
  have htb : b ≫ pullback.fst (i ≫ f) f ≫ i ≫ f = t := by
    rw [pullback.condition, ← Category.assoc, ← h₁, Category.assoc, ← pullback.condition]; exact hta
  have ea := comp_action L i a t hta
  have eb := comp_action L i b t htb
  rw [h₂, eb] at ea
  let : Group (SchemeHomOver t f) := L.pointGroup t
  have hg : (⟨b ≫ pullback.snd (i ≫ f) f, by rw [Category.assoc, ← pullback.condition]; exact htb⟩ :
    SchemeHomOver t f) =
      ⟨a ≫ pullback.snd (i ≫ f) f, by rw [Category.assoc, ← pullback.condition]; exact hta⟩ :=
        Subtype.ext h₁.symm
  have key : ipt i ⟨b ≫ pullback.fst (i ≫ f) f, htb⟩ = ipt i ⟨a ≫ pullback.fst (i ≫ f) f, hta⟩ := by
    have := Subtype.ext ea
    rw [hg] at this
    exact mul_right_cancel this
  have hm := congrArg Subtype.val (ipt_injective i _ _ key)
  apply pullback.hom_ext
  · exact hm.symm
  · exact h₁

include LN hi in
theorem exists_section (hV : q₁ L i j ⁻¹ᵁ V = q₂ L i j ⁻¹ᵁ V) {Y : Scheme.{u}} (π : V.toScheme ⟶ Y)
    (w : (q₁ L i j ∣_ V) ≫ π = (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)) ≫ π)
    (hRπ : IsPullback (q₁ L i j ∣_ V) (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V))
      π π)
    (hU : pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V = L.action i ⁻¹ᵁ Uimg L i j V)
    {C : Scheme.{u}} (c₁ c₂ : C ⟶ (NV (f := f) i j V).toScheme)
    (hc : c₁ ≫ cover L i j V ≫ pdesc L i LN hi j V hV π w = c₂ ≫ cover L i j V ≫ pdesc L i LN hi j V
      hV π w) :
    ∃ s : C ⟶ (pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V).toScheme,
      s ≫ P₁ L i j V = c₁ ≫ cover L i j V ∧ s ≫ P₂ L i j V hU = c₂ ≫ cover L i j V := by
  have h12 : (c₁ ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V)) ≫ π = (c₂ ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_
    V)) ≫ π := by
    rw [Category.assoc, Category.assoc, ← cover_pdesc L i LN hi j V hV π w]; exact hc
  let ρ : C ⟶ pullback (amap L i j) j := hRπ.lift _ _ h12 ≫ (q₁ L i j ⁻¹ᵁ V).ι
  have hρ₁ : ρ ≫ q₁ L i j = (c₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd (i ≫ f) (j ≫ f) := by
    change (hRπ.lift _ _ h12 ≫ (q₁ L i j ⁻¹ᵁ V).ι) ≫ q₁ L i j = _
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hRπ.lift_fst, Category.assoc,
      morphismRestrict_ι,
      Category.assoc]
  have hρ₂ : ρ ≫ q₂ L i j = (c₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd (i ≫ f) (j ≫ f) := by
    have hι : (q₁ L i j ⁻¹ᵁ V).ι ≫ q₂ L i j = (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i
      j ∣_ V)) ≫ V.ι := by
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.isoOfEq_hom_ι]
    change (hRπ.lift _ _ h12 ≫ (q₁ L i j ⁻¹ᵁ V).ι) ≫ q₂ L i j = _
    rw [Category.assoc, hι, ← Category.assoc, hRπ.lift_snd, Category.assoc, morphismRestrict_ι,
      Category.assoc]
  obtain ⟨t, ht₁⟩ : ∃ t : C ⟶ Spec (CommRingCat.of k),
      (c₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _ ≫ i ≫ f = t := ⟨_, rfl⟩
  have eRS : q₁ L i j ≫ j ≫ f = q₂ L i j ≫ j ≫ f := by
    change (pullback.fst (amap L i j) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ≫ j ≫ f = pullback.snd (amap
      L i j) j ≫ j ≫ f
    rw [Category.assoc, ← amap_over, ← Category.assoc, pullback.condition, Category.assoc]
  have ht₂ : (c₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _ ≫ i ≫ f = t := by
    rw [pullback.condition, ← Category.assoc, ← hρ₂, Category.assoc, ← eRS, ← Category.assoc, hρ₁,
      Category.assoc,
      ← pullback.condition]
    exact ht₁
  have ht'' : (ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.fst _ _ ≫ i ≫ f = t := by
    rw [pullback.condition, Category.assoc, ← Category.assoc (pullback.fst (amap L i j) j),
      show (pullback.fst (amap L i j) j ≫ pullback.snd (i ≫ f) (j ≫ f)) = q₁ L i j from rfl, ←
        Category.assoc, hρ₁,
      Category.assoc, ← pullback.condition]
    exact ht₁
  let n : SchemeHomOver t (i ≫ f) := ⟨(c₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _, by
      simpa only [Category.assoc] using ht₁⟩
  let n' : SchemeHomOver t (i ≫ f) := ⟨(c₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _, by
      simpa only [Category.assoc] using ht₂⟩
  let n'' : SchemeHomOver t (i ≫ f) := ⟨(ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.fst _ _, by
      simpa only [Category.assoc] using ht''⟩
  let jv : SchemeHomOver t f := ⟨(c₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j, by
    simp only [Category.assoc]; rw [← pullback.condition]; simpa only [Category.assoc] using ht₁⟩
  let jv' : SchemeHomOver t f := ⟨(c₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j,
    by
    simp only [Category.assoc]; rw [← pullback.condition]; simpa only [Category.assoc] using ht₂⟩
  let : Group (SchemeHomOver t f) := L.pointGroup t
  have rel : L.mul t (ipt i n'') jv = jv' := by
    apply Subtype.ext
    have e1 := comp_amap L i j (ρ ≫ pullback.fst (amap L i j) j) t ht''
    have e2 : (ρ ≫ pullback.fst (amap L i j) j) ≫ amap L i j = (c₂ ≫ (NV (f := f) i j V).ι) ≫
      pullback.snd _ _ ≫ j := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, show ρ ≫ pullback.snd (amap L i j) j
        = _ from hρ₂,
        Category.assoc]
    rw [e2] at e1
    refine (mul_coe_congr L rfl _ _ _ _ rfl ?_).trans e1.symm
    change (c₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j = (ρ ≫ pullback.fst (amap
      L i j) j) ≫ pullback.snd _ _ ≫ j
    rw [← Category.assoc (ρ ≫ _), Category.assoc ρ, show pullback.fst (amap L i j) j ≫ pullback.snd
      (i ≫ f) (j ≫ f) = q₁ L i j from rfl,
      hρ₁]
    simp only [Category.assoc]
  have hc₁ : (c₁ ≫ (NV (f := f) i j V).ι) ≫ amap L i j = (L.mul t (ipt i n) jv).1 := by
    rw [comp_amap L i j _ t ht₁]
  have hc₂ : (c₂ ≫ (NV (f := f) i j V).ι) ≫ amap L i j = (L.mul t (ipt i n') jv').1 := by
    rw [comp_amap L i j _ t ht₂]
  let m : SchemeHomOver t (i ≫ f) := LN.mul t (LN.mul t n' n'') (LN.inv t n)
  have hmg : m.1 ≫ i ≫ f = (L.mul t (ipt i n) jv).1 ≫ f := by rw [m.2, (L.mul t _ _).2]
  let s₀ : C ⟶ pullback (i ≫ f) f := pullback.lift m.1 (L.mul t (ipt i n) jv).1 hmg
  have hs₀snd : s₀ ≫ pullback.snd (i ≫ f) f = (c₁ ≫ (NV (f := f) i j V).ι) ≫ amap L i j := by
    rw [hc₁]; exact pullback.lift_snd _ _ _
  have hs₀act : s₀ ≫ L.action i = (c₂ ≫ (NV (f := f) i j V).ι) ≫ amap L i j := by
    rw [hc₂, comp_action L i s₀ t (by rw [← Category.assoc, pullback.lift_fst]; exact m.2)]
    have hfst : (s₀ ≫ pullback.fst (i ≫ f) f) ≫ i ≫ f = t := by
      rw [← Category.assoc, pullback.lift_fst]
      exact m.2
    have hsnd : (s₀ ≫ pullback.snd (i ≫ f) f) ≫ f = t := by
      rw [pullback.lift_snd]
      exact (L.mul t (ipt i n) jv).2
    have e3 : L.mul t (ipt i ⟨s₀ ≫ pullback.fst (i ≫ f) f, hfst⟩)
        ⟨s₀ ≫ pullback.snd (i ≫ f) f, hsnd⟩ =
        L.mul t (ipt i m) (L.mul t (ipt i n) jv) := by
      apply Subtype.ext; apply mul_coe_congr L rfl
      · simp only [ipt_coe]; rw [pullback.lift_fst]
      · exact pullback.lift_snd _ _ _
    rw [congrArg Subtype.val e3]
    congr 1
    change L.mul t (ipt i (LN.mul t (LN.mul t n' n'') (LN.inv t n))) (L.mul t (ipt i n) jv) = L.mul
      t (ipt i n') jv'
    rw [← rel, ipt_mul L i LN hi, ipt_mul L i LN hi, ipt_inv L i LN hi]
    change ipt i n' * ipt i n'' * (ipt i n)⁻¹ * (ipt i n * jv) = ipt i n' * (ipt i n'' * jv)
    rw [mul_assoc, inv_mul_cancel_left, mul_assoc]
  have hrange : Set.range s₀.base ⊆ Set.range (pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change (s₀ ≫ pullback.snd (i ≫ f) f).base z ∈ (Uimg L i j V : Set ↥G)
    rw [hs₀snd, Category.assoc, ← cover_ι, ← Category.assoc]
    change (Uimg L i j V).ι.base ((c₁ ≫ cover L i j V).base z) ∈ (Uimg L i j V : Set ↥G)
    rw [← Scheme.Opens.range_ι (Uimg L i j V)]; exact ⟨_, rfl⟩
  refine ⟨IsOpenImmersion.lift _ s₀ hrange, ?_, ?_⟩
  · rw [← cancel_mono (Uimg L i j V).ι, Category.assoc, P₁_ι, ← Category.assoc,
      IsOpenImmersion.lift_fac, hs₀snd]
    simp only [Category.assoc, cover_ι]
  · rw [← cancel_mono (Uimg L i j V).ι, Category.assoc, P₂_ι, ← Category.assoc,
      IsOpenImmersion.lift_fac, hs₀act]
    simp only [Category.assoc, cover_ι]

end Effective

section Effective2

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L :
    RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
  (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
  {S : Scheme.{u}} (j : S ⟶ G) (V : S.Opens)
  [UniversallyOpen (amap L i j)] [Flat (amap L i j)] [LocallyOfFinitePresentation (amap L i j)]
  (hV : q₁ L i j ⁻¹ᵁ V = q₂ L i j ⁻¹ᵁ V) {Y : Scheme.{u}} (π : V.toScheme ⟶ Y)
  (w : (q₁ L i j ∣_ V) ≫ π = (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)) ≫ π)
  (hRπ : IsPullback (q₁ L i j ∣_ V) (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)) π
    π)
  (hU : pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V = L.action i ⁻¹ᵁ Uimg L i j V)

include LN hi hRπ in
theorem effective :
    IsPullback (P₁ L i j V) (P₂ L i j V hU) (pdesc L i LN hi j V hV π w) (pdesc L i LN hi j V hV π
      w) := by
  have sq : P₁ L i j V ≫ pdesc L i LN hi j V hV π w = P₂ L i j V hU ≫ pdesc L i LN hi j V hV π w :=
    square L i LN hi j V hV π w hU
  let κ := pullback.lift (P₁ L i j V) (P₂ L i j V hU) sq
  have hκ₁ : κ ≫ pullback.fst _ _ = P₁ L i j V := pullback.lift_fst _ _ _
  have hκ₂ : κ ≫ pullback.snd _ _ = P₂ L i j V hU := pullback.lift_snd _ _ _
  have : Mono κ := ⟨fun {T} a b h => by
    have h1 : a ≫ P₁ L i j V = b ≫ P₁ L i j V := by rw [← hκ₁, ← Category.assoc, h, Category.assoc]
    have h2 : a ≫ P₂ L i j V hU = b ≫ P₂ L i j V hU := by rw [← hκ₂, ← Category.assoc, h,
      Category.assoc]
    rw [← cancel_mono (pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V).ι]
    apply eq_of_snd_eq_of_action_eq L i
    · rw [Category.assoc, Category.assoc, ← P₁_ι, ← Category.assoc, h1, Category.assoc]
    · rw [Category.assoc, Category.assoc, ← P₂_ι L i j V hU, ← Category.assoc, h2, Category.assoc]⟩
  let pp := pdesc L i LN hi j V hV π w
  let d₁ := pullback.fst (pullback.fst pp pp) (cover L i j V)
  let e₁ := pullback.fst (d₁ ≫ pullback.snd pp pp) (cover L i j V)
  let cc := e₁ ≫ d₁
  let c₁ := e₁ ≫ pullback.snd (pullback.fst pp pp) (cover L i j V)
  let c₂ := pullback.snd (d₁ ≫ pullback.snd pp pp) (cover L i j V)
  have hcc₁ : cc ≫ pullback.fst pp pp = c₁ ≫ cover L i j V := by
    change (e₁ ≫ d₁) ≫ pullback.fst pp pp = (e₁ ≫ pullback.snd (pullback.fst pp pp) (cover L i j V))
      ≫ cover L i j V
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hcc₂ : cc ≫ pullback.snd pp pp = c₂ ≫ cover L i j V := by
    change (e₁ ≫ d₁) ≫ pullback.snd pp pp = _
    rw [Category.assoc]; exact pullback.condition
  have hc : c₁ ≫ cover L i j V ≫ pp = c₂ ≫ cover L i j V ≫ pp := by
    rw [← Category.assoc, ← hcc₁, Category.assoc, pullback.condition, ← Category.assoc, hcc₂,
      Category.assoc]
  obtain ⟨s, hs₁, hs₂⟩ := exists_section L i LN hi j V hV π w hRπ hU c₁ c₂ hc
  have hsκ : s ≫ κ = cc := by
    apply pullback.hom_ext
    · rw [Category.assoc, hκ₁, hs₁, hcc₁]
    · rw [Category.assoc, hκ₂, hs₂, hcc₂]
  have hsplit : IsSplitEpi (pullback.fst cc κ) :=
    IsSplitEpi.mk' ⟨pullback.lift (𝟙 _) s (by rw [Category.id_comp, hsκ]), pullback.lift_fst _ _ _⟩
  have hiso : IsIso (pullback.fst cc κ) := isIso_of_mono_of_isSplitEpi _
  have hQ : (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) cc :=
    ⟨⟨(inferInstance : Surjective (e₁ ≫ d₁)), (inferInstance : Flat (e₁ ≫ d₁))⟩,
      (inferInstance : LocallyOfFinitePresentation (e₁ ≫ d₁))⟩
  have hκ : IsIso κ := (MorphismProperty.isomorphisms.iff κ).1
    (MorphismProperty.of_pullback_fst_of_descendsAlong (P := MorphismProperty.isomorphisms
      Scheme.{u})
      (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) hQ
        ((MorphismProperty.isomorphisms.iff _).2 hiso))
  exact IsPullback.of_iso_pullback ⟨sq⟩ (asIso κ) hκ₁ hκ₂

end Effective2

end SliceDescent

end

end AbelianVarieties.NOSProofs.QuotientSliceDescent

namespace GoodReductionJacobian.RelativeGroupLaw

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AbelianVarieties.NOSProofs.QuotientSliceDescent.SliceDescent

theorem exists_opens_saturated_fppf_quotient_of_sliceQuotient
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (S : Scheme.{u}) (j : S ⟶ G) [IsAffine S] [LocallyOfFiniteType (j ≫ f)]
    (hEt : Etale (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i))
    (V : S.Opens) (hV : (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫
      f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i)
            j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ V =
            (CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f)
            (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i)
            j) ⁻¹ᵁ V) [Nonempty (V.toScheme)]
    {Y : Scheme.{u}} (π : V.toScheme ⟶ Y) (w : ((CategoryTheory.Limits.pullback.fst
      (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i)
            j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) ≫ π =
            (((CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i
            ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i)
            j).isoOfEq hV).hom ≫ ((CategoryTheory.Limits.pullback.snd
            (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i)
            j) ∣_ V)) ≫ π)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π] [Surjective π]
    (hRπ : IsPullback ((CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫
      f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i)
            j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ∣_ V)
            (((CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i
            ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i)
            j).isoOfEq hV).hom ≫ ((CategoryTheory.Limits.pullback.snd
            (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i)
            j) ∣_ V)) π π) (hcoeq : IsColimit (Cofork.ofπ π w)) :
    ∃ (U : G.Opens) (hU : CategoryTheory.Limits.pullback.snd (i ≫ f) f ⁻¹ᵁ U = L.action i ⁻¹ᵁ U),
      Nonempty (U.toScheme) ∧
      ∃ (Y : Scheme.{u}) (p : (U).toScheme ⟶ Y),
        (CategoryTheory.Limits.pullback.snd (i ≫ f) f ∣_ U) ≫ p =
          (((CategoryTheory.Limits.pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ U)) ≫ p ∧
        Flat p ∧ LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ Surjective p ∧
        IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f ∣_ U)
          (((CategoryTheory.Limits.pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ U)) p p
            := by
  have : Etale _ := hEt
  have : Smooth (amap L i j) := inferInstance
  have : Flat (amap L i j) := inferInstance
  have : LocallyOfFinitePresentation (amap L i j) := inferInstance
  have : UniversallyOpen (amap L i j) := inferInstance
  have : Smooth (i ≫ f) := SmoothOfRelativeDimension.smooth h _
  have : Flat (i ≫ f) := inferInstance
  have : QuasiCompact (i ≫ f) := inferInstance
  have : Smooth f := SmoothOfRelativeDimension.smooth g f
  have : LocallyOfFinitePresentation f := inferInstance
  have : LocallyOfFiniteType f := inferInstance
  have hU := Uimg_saturated L i LN hi j V
  refine ⟨Uimg L i j V, hU, nonempty_Uimg L i LN j V, Y, pdesc L i LN hi j V hV π w,
    square L i LN hi j V hV π w hU, flat_pdesc L i LN hi j V hV π w,
    locallyOfFinitePresentation_pdesc L i LN hi j V hV π w hcoeq, quasiCompact_pdesc L i LN hi j V
      hV π w,
    surjective_pdesc L i LN hi j V hV π w, effective L i LN hi j V hV π w hRπ hU⟩

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_fppf_quotient_of_isClosedImmersion_of_isAlgClosed.lean
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

theorem exists_opens_saturated_fppf_quotient_of_isClosedImmersion_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) :
    ∃ (U : G.Opens) (hU : CategoryTheory.Limits.pullback.snd (i ≫ f) f ⁻¹ᵁ U = L.action i ⁻¹ᵁ U),
      Nonempty (U.toScheme) ∧
      ∃ (Y : Scheme.{u}) (p : (U).toScheme ⟶ Y),
        (CategoryTheory.Limits.pullback.snd (i ≫ f) f ∣_ U) ≫ p =
          (((CategoryTheory.Limits.pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ U)) ≫ p ∧
        Flat p ∧ LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ Surjective p ∧
        IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f ∣_ U)
          (((CategoryTheory.Limits.pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ U)) p p
            := by
  obtain ⟨S, j, hSaff, hSne, hSsm, hEt⟩ :=
    exists_affine_etale_slice_of_isAlgClosed k f L g i LN h hi
  have : IsAffine _ := hSaff
  have : Nonempty _ := hSne
  have : SmoothOfRelativeDimension _ _ := hSsm
  have : Smooth (j ≫ f) := SmoothOfRelativeDimension.smooth (g - h) (j ≫ f)
  have : LocallyOfFiniteType (j ≫ f) := inferInstance
  obtain ⟨V, hV, hVne, hf1, hfl1, hlfp1, hf2, hfl2, hlfp2, hmono, hequiv, haff⟩ :=
    exists_opens_saturated_finiteLocallyFree_sliceRelation_of_etale
      k f L g i LN h hi S j hEt
  have : Nonempty _ := hVne
  have : IsFinite _ := hf1
  have : Flat _ := hfl1
  have : LocallyOfFinitePresentation _ := hlfp1
  have : IsFinite _ := hf2
  have : Flat _ := hfl2
  have : LocallyOfFinitePresentation _ := hlfp2
  obtain ⟨Y, π, w, hπf, hπfl, hπlfp, hπsurj, hRπ, ⟨hcoeq⟩⟩ :=
    AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation _ _ hmono
      hequiv haff
  have : IsFinite _ := hπf
  have : Flat _ := hπfl
  have : LocallyOfFinitePresentation _ := hπlfp
  have : Surjective _ := hπsurj
  exact exists_opens_saturated_fppf_quotient_of_sliceQuotient
    k f L g i LN h hi S j hEt V hV π w hRπ hcoeq

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_fppf_quotient_isPullback_action_of_isClosedImmersion.lean
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

theorem exists_fppf_quotient_isPullback_action_of_isClosedImmersion
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (_hnormal : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f)
      (n : SchemeHomOver t (i ≫ f)), ∃ n' : SchemeHomOver t (i ≫ f),
        NeronModelInfra.schemeHomOverComp n' (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (L.mul t x (NeronModelInfra.schemeHomOverComp n (⟨i, rfl⟩ : SchemeHomOver (i ≫ f)
            f)))
            (L.inv t x)) :
    ∃ (Q : Scheme.{u}) (fQ : Q ⟶ Spec (CommRingCat.of k)) (q : G ⟶ Q)
      (w : CategoryTheory.Limits.pullback.snd (i ≫ f) f ≫ q = L.action i ≫ q),
      q ≫ fQ = f ∧ IsSeparated fQ ∧ QuasiCompact fQ ∧
      Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧
      IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f) (L.action i) q q ∧
      Nonempty (IsColimit (Cofork.ofπ q w)) := by
  classical
  obtain ⟨hst, -, -, -⟩ :=
    action_shear_and_equivalence_of_isClosedImmersion L i LN hi
  obtain ⟨U, hU, hne, hloc⟩ :=
    exists_opens_saturated_fppf_quotient_of_isClosedImmersion_of_isAlgClosed k f L g i LN h hi
  have : Nonempty _ := hne
  have : Smooth f := SmoothOfRelativeDimension.smooth g f
  have cover :=
    forall_exists_opens_saturated_fppf_quotient_of_isAlgClosed k f L i U hU hloc
  choose W hW hxW hlocW using cover
  obtain ⟨Q, q, w, hflat, hlfp, hqc, hsurj, hR, ⟨hcoeq⟩⟩ :=
    AlgebraicGeometry.Scheme.exists_fppf_quotient_of_forall_exists_quotient_restrict
      (CategoryTheory.Limits.pullback.snd (i ≫ f) f) (L.action i) W hxW hW hlocW
  let fQ : Q ⟶ Spec (CommRingCat.of k) := hcoeq.desc (Cofork.ofπ f hst.symm)
  have hq : q ≫ fQ = f := hcoeq.fac (Cofork.ofπ f hst.symm) Limits.WalkingParallelPair.one
  have : Flat _ := hflat
  have : LocallyOfFinitePresentation _ := hlfp
  have : QuasiCompact _ := hqc
  have : Surjective _ := hsurj
  obtain ⟨hsep, hqc'⟩ :=
    isSeparated_and_quasiCompact_of_isPullback_action_of_surjective k f L i fQ q hq hR
  exact ⟨Q, fQ, q, w, hq, hsep, hqc', hflat, hlfp, hsurj, hR, ⟨hcoeq⟩⟩

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_quotient_smoothOfRelativeDimension_sub_of_isClosedImmersion_of_isAlgClosed.lean
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

theorem exists_quotient_smoothOfRelativeDimension_sub_of_isClosedImmersion_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (hnormal : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f)
      (n : SchemeHomOver t (i ≫ f)), ∃ n' : SchemeHomOver t (i ≫ f),
        NeronModelInfra.schemeHomOverComp n' (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (L.mul t x (NeronModelInfra.schemeHomOverComp n (⟨i, rfl⟩ : SchemeHomOver (i ≫ f)
            f)))
            (L.inv t x)) :
    ∃ (Q : Scheme.{u}) (fQ : Q ⟶ Spec (CommRingCat.of k)) (LQ : RelativeGroupLaw k fQ)
      (q : SchemeHomOver f fQ),
      IsSeparated fQ ∧ QuasiCompact fQ ∧ SmoothOfRelativeDimension (g - h) fQ ∧ h ≤ g ∧
      SmoothOfRelativeDimension h q.1 ∧ Surjective q.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
        NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
          LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q))
            ∧
      (L.IsCommutative → LQ.IsCommutative) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
        NeronModelInfra.schemeHomOverComp x q = LQ.one t ↔
          ∃ y : SchemeHomOver t (i ≫ f),
            NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = x) := by
  obtain ⟨Q, fQ, q, w, hq, hsep, hqc, hflat, hlfp, hsurj, hR, ⟨hcoeq⟩⟩ :=
    exists_fppf_quotient_isPullback_action_of_isClosedImmersion
      k f L g i LN h hi hnormal
  have : Flat _ := hflat
  have : LocallyOfFinitePresentation _ := hlfp
  have : Surjective _ := hsurj
  have : IsSeparated _ := hsep
  have hqqc : QuasiCompact q := by
    have : QuasiCompact (q ≫ fQ) := by rw [hq]; infer_instance
    exact QuasiCompact.of_comp q fQ
  let q' : SchemeHomOver f fQ := ⟨q, hq⟩
  obtain ⟨LQ, hhom, hcomm, hker⟩ :=
    exists_relativeGroupLaw_quotient_of_isPullback_action_of_surjective
      L i LN hi hnormal q' w hR hcoeq
  have : Nonempty N := ⟨(LN.one (𝟙 _)).1.base (show Spec (CommRingCat.of k) from
    IsLocalRing.closedPoint k)⟩
  obtain ⟨hqs, hQs, hle⟩ :=
    smoothOfRelativeDimension_of_isPullback_action_of_surjective
      k f L g i h fQ q hq hR
  exact ⟨Q, fQ, LQ, q', hsep, hqc, hQs, hle, hqs, hsurj, hhom, hcomm, hker⟩

end GoodReductionJacobian.RelativeGroupLaw
end
