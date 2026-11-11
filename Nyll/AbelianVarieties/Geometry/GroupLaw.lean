/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Nyll.SchemeTheory.BaseChange.SchemeHomOver
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawSchemeNsmulCompEqCompSchemeNsmul
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Kernel
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Basic
public import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.RelativeGroupLawGrpObj
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Relative group laws, translations and kernels

Construct translation and shear isomorphisms and compare relative kernels and torsor products.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_one_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.TranslationAutomorphisms


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace Translations

variable {k : Type u} [CommRing k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L :
    RelativeGroupLaw k f)

/-- The identity point of the group scheme, using the shared relative-morphism identity. -/
abbrev idPt (f : G ⟶ Spec (CommRingCat.of k)) : SchemeHomOver f f :=
  NeronModelInfra.schemeHomOverId f

/-- The constant relative point induced by a point over the base. -/
def const (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) {T : Scheme.{u}} (t : T ⟶ Spec
    (CommRingCat.of k)) :
    SchemeHomOver t f :=
  schemeHomOverComp t (Category.comp_id t) a

@[scoped simp]
theorem const_coe (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) : (const a t).1 = t ≫ a.1 := rfl

theorem comp_const (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t =
      t') :
    schemeHomOverComp ψ hψ (const a t) = const a t' := by
  apply Subtype.ext
  change ψ ≫ (t ≫ a.1) = t' ≫ a.1
  rw [← Category.assoc, hψ]

/-- Right translation by a point over the base. -/
def rt (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : G ⟶ G :=
  (L.mul f (idPt f) (const a f)).1

theorem rt_over (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : rt L a ≫ f = f :=
  (L.mul f (idPt f) (const a f)).2

theorem comp_rt (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f) :
    P.1 ≫ rt L a = (L.mul t P (const a t)).1 := by
  have hP : schemeHomOverComp P.1 P.2 (idPt f) = P := Subtype.ext (Category.comp_id _)
  have := L.mul_natural f t P.1 P.2 (idPt f) (const a f)
  rw [hP, comp_const] at this
  rw [← this]
  rfl

theorem rt_mul (a b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    rt L a ≫ rt L b = rt L (L.mul (𝟙 _) a b) := by
  have h1 : rt L a ≫ rt L b = (L.mul f (L.mul f (idPt f) (const a f)) (const b f)).1 := by
    rw [← comp_rt L b f]; rfl
  rw [h1, L.mul_assoc]
  have h2 : L.mul f (const a f) (const b f) = const (L.mul (𝟙 _) a b) f := by
    simp only [const]
    rw [← L.mul_natural (𝟙 _) f f (Category.comp_id f)]
  rw [h2]; rfl

theorem rt_one : rt L (L.one (𝟙 _)) = 𝟙 G := by
  have : const (L.one (𝟙 (Spec (CommRingCat.of k)))) f = L.one f := L.one_natural (𝟙 _) f f
    (Category.comp_id f)
  change (L.mul f (idPt f) (const (L.one (𝟙 _)) f)).1 = 𝟙 G
  rw [this, L.mul_one]
  rfl

/-- Right translation as an automorphism of the group scheme. -/
def rtIso (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : G ≅ G where
  hom := rt L a
  inv := rt L (L.inv (𝟙 _) a)
  hom_inv_id := by rw [rt_mul, L.mul_inv_cancel, rt_one]
  inv_hom_id := by rw [rt_mul, L.inv_mul_cancel, rt_one]

scoped instance (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : IsIso (rt L a) := (rtIso L
    a).isIso_hom

end Translations

end

theorem _root_.GoodReductionJacobian.RelativeGroupLaw.exists_iso_hom_comp_eq_one_comp_eq
    {R : Type u} [CommRing R] {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of R)} (L :
      RelativeGroupLaw R g)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) g) :
    ∃ τ : X ≅ X, τ.hom ≫ g = g ∧ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ τ.hom = a.1 := by
  refine ⟨Translations.rtIso L a, Translations.rt_over L a, ?_⟩
  change (L.one (𝟙 _)).1 ≫ Translations.rt L a = a.1
  rw [Translations.comp_rt, L.one_mul]
  change 𝟙 _ ≫ a.1 = a.1
  rw [Category.id_comp]

end AbelianVarieties.NOSProofs.TranslationAutomorphisms
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.GroupObjects

open AlgebraicGeometry CategoryTheory CategoryTheory.CartesianMonoidalCategory NeronModelInfra
    GoodReductionJacobian

universe u

theorem _root_.GoodReductionJacobian.RelativeGroupLaw.exists_grpObj_eq
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) :
    ∃ g : GrpObj (Over.mk f),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : Over.mk t ⟶ Over.mk f),
        overHomToSchemeHomOver (lift a b ≫ g.mul) =
          G.mul t (overHomToSchemeHomOver a) (overHomToSchemeHomOver b)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        overHomToSchemeHomOver (toUnit (Over.mk t) ≫ g.one) = G.one t) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : Over.mk t ⟶ Over.mk f),
        overHomToSchemeHomOver (a ≫ g.inv) = G.inv t (overHomToSchemeHomOver a)) :=
  ⟨G.grpObjOverMk, fun t a b => G.overHomToSchemeHomOver_mul t a b,
    fun t => G.overHomToSchemeHomOver_one t, fun t a => G.overHomToSchemeHomOver_inv t a⟩

end AbelianVarieties.NOSProofs.GroupObjects
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isPullback_mul_fst.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.MultiplicationPullback


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u


variable {R : Type u} [CommRing R] {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of R)}
  (LG : RelativeGroupLaw R g)

/-- Restricting a relative point commutes with inversion. -/
lemma _root_.GoodReductionJacobian.RelativeGroupLaw.inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec
    (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t g) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (LG.inv t x) =
      LG.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  have hyz : LG.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (LG.inv t x))
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = LG.one t' := by
    rw [← LG.mul_natural t t' ψ hψ, LG.inv_mul_cancel, LG.one_natural]
  calc GoodReductionJacobian.schemeHomOverComp ψ hψ (LG.inv t x)
      = LG.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (LG.inv t x)) (LG.one t') :=
        (LG.mul_one t' _).symm
    _ = LG.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (LG.inv t x))
          (LG.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x)
            (LG.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x))) := by rw
              [LG.mul_inv_cancel]
    _ = LG.mul t' (LG.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (LG.inv t x))
          (GoodReductionJacobian.schemeHomOverComp ψ hψ x))
          (LG.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x)) := by rw [LG.mul_assoc]
    _ = LG.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by rw [hyz, LG.one_mul]

theorem _root_.GoodReductionJacobian.RelativeGroupLaw.isPullback_mul_fst
    {R : Type u} [CommRing R] {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of R)} (LG :
      RelativeGroupLaw R g) :
    IsPullback
      (LG.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩ ⟨pullback.snd g g,
        pullback.condition.symm⟩).1
      (pullback.fst g g) g g := by
  set A : SchemeHomOver (pullback.fst g g ≫ g) g := ⟨pullback.fst g g, rfl⟩ with hA
  set B : SchemeHomOver (pullback.fst g g ≫ g) g := ⟨pullback.snd g g, pullback.condition.symm⟩ with
    hB
  have wφ : pullback.fst g g ≫ g = (LG.mul _ A B).1 ≫ g := (LG.mul _ A B).2.symm
  have wψ : pullback.fst g g ≫ g = (LG.mul _ (LG.inv _ A) B).1 ≫ g := (LG.mul _ (LG.inv _ A)
    B).2.symm
  let φ : pullback g g ⟶ pullback g g := pullback.lift (pullback.fst g g) (LG.mul _ A B).1 wφ
  let ψ : pullback g g ⟶ pullback g g := pullback.lift (pullback.fst g g) (LG.mul _ (LG.inv _ A)
    B).1 wψ
  have hφ₁ : φ ≫ pullback.fst g g = pullback.fst g g := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ pullback.snd g g = (LG.mul _ A B).1 := pullback.lift_snd _ _ _
  have hψ₁ : ψ ≫ pullback.fst g g = pullback.fst g g := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd g g = (LG.mul _ (LG.inv _ A) B).1 := pullback.lift_snd _ _ _
  have hφt : φ ≫ pullback.fst g g ≫ g = pullback.fst g g ≫ g := by rw [← Category.assoc, hφ₁]
  have hψt : ψ ≫ pullback.fst g g ≫ g = pullback.fst g g ≫ g := by rw [← Category.assoc, hψ₁]
  have hφA : GoodReductionJacobian.schemeHomOverComp φ hφt A = A := Subtype.ext hφ₁
  have hφB : GoodReductionJacobian.schemeHomOverComp φ hφt B = LG.mul _ A B := Subtype.ext hφ₂
  have hψA : GoodReductionJacobian.schemeHomOverComp ψ hψt A = A := Subtype.ext hψ₁
  have hψB : GoodReductionJacobian.schemeHomOverComp ψ hψt B = LG.mul _ (LG.inv _ A) B :=
    Subtype.ext hψ₂
  have h1 : φ ≫ (LG.mul _ (LG.inv _ A) B).1 = pullback.snd g g := by
    change (GoodReductionJacobian.schemeHomOverComp φ hφt (LG.mul _ (LG.inv _ A) B)).1 = B.1
    rw [LG.mul_natural _ _ φ hφt, LG.inv_natural _ _ φ hφt, hφA, hφB, ← LG.mul_assoc,
      LG.inv_mul_cancel, LG.one_mul]
  have h2 : ψ ≫ (LG.mul _ A B).1 = pullback.snd g g := by
    change (GoodReductionJacobian.schemeHomOverComp ψ hψt (LG.mul _ A B)).1 = B.1
    rw [LG.mul_natural _ _ ψ hψt, hψA, hψB, ← LG.mul_assoc, LG.mul_inv_cancel, LG.one_mul]
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, hψ₁, hφ₁]
    · rw [Category.id_comp, Category.assoc, hψ₂, h1]
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, hφ₁, hψ₁]
    · rw [Category.id_comp, Category.assoc, hφ₂, h2]
  exact (IsPullback.of_hasPullback g g).flip.of_iso ⟨ψ, φ, hψφ, hφψ⟩ (Iso.refl _) (Iso.refl _)
    (Iso.refl _)
    (by rw [Iso.refl_hom, Category.comp_id]; exact h2.symm)
    (by rw [Iso.refl_hom, Category.comp_id]; exact hψ₁.symm)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])

end AbelianVarieties.NOSProofs.MultiplicationPullback
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.ShearIsomorphisms


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

universe u

noncomputable section

namespace GoodReductionJacobian
open _root_.GoodReductionJacobian
namespace RelativeGroupLaw
open _root_.GoodReductionJacobian.RelativeGroupLaw
namespace Shear
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian

variable {R : Type u} [CommRing R] {G T : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R g) (t : T ⟶ Spec (CommRingCat.of R))

/-- The group coordinate of the base-changed product. -/
def prG : SchemeHomOver (pullback.fst t g ≫ t) g := ⟨pullback.snd t g, pullback.condition.symm⟩

/-- Pull a relative group point back along the first projection of the product. -/
def lift (b : SchemeHomOver t g) : SchemeHomOver (pullback.fst t g ≫ t) g :=
  ⟨pullback.fst t g ≫ b.1, by rw [Category.assoc, b.2]⟩

lemma lift_eq (b : SchemeHomOver t g) :
    lift t b = GoodReductionJacobian.schemeHomOverComp (pullback.fst t g) rfl b := rfl

/-- Multiply the group coordinate by the given relative point. -/
def shear (b : SchemeHomOver t g) : pullback t g ⟶ pullback t g :=
  pullback.lift (pullback.fst t g) (L.mul (pullback.fst t g ≫ t) (lift t b) (prG t)).1
    (L.mul (pullback.fst t g ≫ t) (lift t b) (prG t)).2.symm

@[scoped simp] lemma shear_fst (b : SchemeHomOver t g) : shear L t b ≫ pullback.fst t g =
    pullback.fst t g :=
  pullback.lift_fst _ _ _

@[scoped simp] lemma shear_snd (b : SchemeHomOver t g) :
    shear L t b ≫ pullback.snd t g = (L.mul (pullback.fst t g ≫ t) (lift t b) (prG t)).1 :=
  pullback.lift_snd _ _ _

lemma mul_lift (b c : SchemeHomOver t g) :
    L.mul (pullback.fst t g ≫ t) (lift t b) (lift t c) = lift t (L.mul t b c) := by
  rw [lift_eq, lift_eq, lift_eq, ← L.mul_natural]

lemma shear_comp_shear (b c : SchemeHomOver t g) :
    shear L t b ≫ shear L t c = shear L t (L.mul t c b) := by
  have hψ : shear L t b ≫ pullback.fst t g ≫ t = pullback.fst t g ≫ t := by
    rw [← Category.assoc, shear_fst]
  apply pullback.hom_ext
  · simp only [Category.assoc, shear_fst]
  · simp only [Category.assoc, shear_snd]
    have nat := congrArg Subtype.val
      (L.mul_natural (pullback.fst t g ≫ t) (pullback.fst t g ≫ t) (shear L t b) hψ (lift t c) (prG
        t))
    simp only [GoodReductionJacobian.schemeHomOverComp_coe] at nat
    rw [nat]
    have h1 : GoodReductionJacobian.schemeHomOverComp (shear L t b) hψ (lift t c) = lift t c := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, lift, ← Category.assoc, shear_fst]
    have h2 : GoodReductionJacobian.schemeHomOverComp (shear L t b) hψ (prG t) =
        L.mul (pullback.fst t g ≫ t) (lift t b) (prG t) := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, prG, shear_snd]
    rw [h1, h2, ← L.mul_assoc, mul_lift]

lemma shear_one : shear L t (L.one t) = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [shear_fst, Category.id_comp]
  · simp only [shear_snd, Category.id_comp]
    have : lift t (L.one t) = L.one (pullback.fst t g ≫ t) := by
      rw [lift_eq, L.one_natural]
    rw [this, L.one_mul]
    rfl

/-- The shear map as an automorphism of the base-changed product. -/
def shearIso (a : SchemeHomOver t g) : pullback t g ≅ pullback t g where
  hom := shear L t a
  inv := shear L t (L.inv t a)
  hom_inv_id := by rw [shear_comp_shear, L.inv_mul_cancel, shear_one]
  inv_hom_id := by rw [shear_comp_shear, L.mul_inv_cancel, shear_one]

end GoodReductionJacobian.RelativeGroupLaw.Shear

end

open GoodReductionJacobian.RelativeGroupLaw.Shear in
theorem
    _root_.GoodReductionJacobian.RelativeGroupLaw.exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul
    {R : Type u} [CommRing R] {G T : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R g) (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t g) :
    ∃ σ : pullback t g ≅ pullback t g,
      σ.hom ≫ pullback.fst t g = pullback.fst t g ∧
      σ.hom ≫ pullback.snd t g =
        (L.mul (pullback.fst t g ≫ t) ⟨pullback.fst t g ≫ a.1, by rw [Category.assoc, a.2]⟩
          ⟨pullback.snd t g, pullback.condition.symm⟩).1 :=
  ⟨shearIso L t a, shear_fst L t a, shear_snd L t a⟩

end AbelianVarieties.NOSProofs.ShearIsomorphisms
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_and_comp_hom_eq_mul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.TranslationFormulas


universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace Translation

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem inv_natural (L : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t =
      t')
    (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) :=
  L.inv_natural t t' ψ hψ x

end Translation

open Translation in
theorem _root_.GoodReductionJacobian.RelativeGroupLaw.exists_iso_hom_comp_eq_and_comp_hom_eq_mul
    (R : Type u) [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : GoodReductionJacobian.RelativeGroupLaw R f)
    (d : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    ∃ τ : A ≅ A, τ.hom ≫ f = f ∧ τ.inv ≫ f = f ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : NeronModelInfra.SchemeHomOver t f),
        x.1 ≫ τ.hom = (L.mul t x (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t)
          d)).1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : NeronModelInfra.SchemeHomOver t f),
        x.1 ≫ τ.inv = (L.mul t x (L.inv t (GoodReductionJacobian.schemeHomOverComp t
          (Category.comp_id t) d))).1) := by
  let e : SchemeHomOver f f := ⟨𝟙 A, Category.id_comp f⟩
  let dA : SchemeHomOver f f := schemeHomOverComp f (Category.comp_id f) d
  let th : A ⟶ A := (L.mul f e dA).1
  let ti : A ⟶ A := (L.mul f e (L.inv f dA)).1
  have hth : th ≫ f = f := (L.mul f e dA).2
  have hti : ti ≫ f = f := (L.mul f e (L.inv f dA)).2
  have key : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (y :
    SchemeHomOver f f),
      x.1 ≫ (L.mul f e y).1 = (L.mul t x (schemeHomOverComp x.1 x.2 y)).1 := by
    intro T t x y
    have h := congrArg Subtype.val (L.mul_natural f t x.1 x.2 e y)
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
    rw [h]
    have hx : schemeHomOverComp x.1 x.2 e = x := Subtype.ext (Category.comp_id _)
    rw [hx]
  have hdA : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      schemeHomOverComp x.1 x.2 dA = schemeHomOverComp t (Category.comp_id t) d := by
    intro T t x
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, dA]
    rw [← Category.assoc, x.2]
  have hpt : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      x.1 ≫ th = (L.mul t x (schemeHomOverComp t (Category.comp_id t) d)).1 := by
    intro T t x
    rw [key t x dA, hdA t x]
  have hpt' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      x.1 ≫ ti = (L.mul t x (L.inv t (schemeHomOverComp t (Category.comp_id t) d))).1 := by
    intro T t x
    rw [key t x (L.inv f dA), inv_natural L f t x.1 x.2 dA, hdA t x]
  have h1 : th ≫ ti = 𝟙 A := by
    have h := hpt' f ⟨th, hth⟩
    rw [h]
    have hth' : (⟨th, hth⟩ : SchemeHomOver f f) = L.mul f e dA := rfl
    rw [hth']
    change (L.mul f (L.mul f e dA) (L.inv f dA)).1 = 𝟙 A
    rw [L.mul_assoc, L.mul_inv_cancel, L.mul_one]
  have h2 : ti ≫ th = 𝟙 A := by
    have h := hpt f ⟨ti, hti⟩
    rw [h]
    have hti' : (⟨ti, hti⟩ : SchemeHomOver f f) = L.mul f e (L.inv f dA) := rfl
    rw [hti']
    change (L.mul f (L.mul f e (L.inv f dA)) dA).1 = 𝟙 A
    rw [L.mul_assoc, L.inv_mul_cancel, L.mul_one]
  exact ⟨⟨th, ti, h1, h2⟩, hth, hti, fun t x => hpt t x, fun t x => hpt' t x⟩

end AbelianVarieties.NOSProofs.TranslationFormulas
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_pullback_iso_pullback_of_comp_eq_one_iff.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.KernelTorsor


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace Torsor

variable {k : Type u} [CommRing k]

theorem map_one {G Q : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} {fQ : Q ⟶ Spec (CommRingCat.of
    k)}
    (L : RelativeGroupLaw k f) (LQ : RelativeGroupLaw k fQ) (q : SchemeHomOver f fQ)
    (hq : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
        LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    NeronModelInfra.schemeHomOverComp (L.one t) q = LQ.one t := by
  let : Group (SchemeHomOver t fQ) := LQ.pointGroup t
  have h : NeronModelInfra.schemeHomOverComp (L.one t) q * NeronModelInfra.schemeHomOverComp (L.one
    t) q =
      NeronModelInfra.schemeHomOverComp (L.one t) q := by
    change LQ.mul t _ _ = _
    rw [← hq, L.one_mul]
  exact mul_eq_right.mp h

theorem map_inv {G Q : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} {fQ : Q ⟶ Spec (CommRingCat.of
    k)}
    (L : RelativeGroupLaw k f) (LQ : RelativeGroupLaw k fQ) (q : SchemeHomOver f fQ)
    (hq : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
        LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (L.inv t x) q = LQ.inv t (NeronModelInfra.schemeHomOverComp x
      q) := by
  let : Group (SchemeHomOver t fQ) := LQ.pointGroup t
  have h : NeronModelInfra.schemeHomOverComp (L.inv t x) q * NeronModelInfra.schemeHomOverComp x q =
    1 := by
    change LQ.mul t _ _ = LQ.one t
    rw [← hq, L.inv_mul_cancel, map_one L LQ q hq]
  exact eq_inv_of_mul_eq_one_left h

theorem inv_natural {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (t' : T' ⟶ Spec (CommRingCat.of k))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) =
      L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) :=
  L.inv_natural t t' ψ hψ x

end Torsor

theorem
    _root_.GoodReductionJacobian.RelativeGroupLaw.exists_pullback_iso_pullback_of_comp_eq_one_iff
    (k : Type u) [CommRing k]
    {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i]
    {Q : Scheme.{u}} (fQ : Q ⟶ Spec (CommRingCat.of k)) (LQ : RelativeGroupLaw k fQ)
    (q : SchemeHomOver f fQ)
    (hq : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
        LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q))
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp x q = LQ.one t ↔
        ∃ y : SchemeHomOver t (i ≫ f),
          NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = x) :
    ∃ e : pullback q.1 q.1 ≅ pullback (i ≫ f) f, e.hom ≫ pullback.snd (i ≫ f) f = pullback.snd q.1
      q.1 := by
  classical
  let t : pullback q.1 q.1 ⟶ Spec (CommRingCat.of k) := pullback.snd q.1 q.1 ≫ f
  have hfst : pullback.fst q.1 q.1 ≫ f = t := by
    change _ = pullback.snd q.1 q.1 ≫ f
    calc pullback.fst q.1 q.1 ≫ f = (pullback.fst q.1 q.1 ≫ q.1) ≫ fQ := by rw [Category.assoc, q.2]
      _ = (pullback.snd q.1 q.1 ≫ q.1) ≫ fQ := by rw [pullback.condition]
      _ = pullback.snd q.1 q.1 ≫ f := by rw [Category.assoc, q.2]
  let x : SchemeHomOver t f := ⟨pullback.fst q.1 q.1, hfst⟩
  let y : SchemeHomOver t f := ⟨pullback.snd q.1 q.1, rfl⟩
  have hxy : NeronModelInfra.schemeHomOverComp x q = NeronModelInfra.schemeHomOverComp y q :=
    Subtype.ext pullback.condition
  let z : SchemeHomOver t f := L.mul t x (L.inv t y)
  have hz : NeronModelInfra.schemeHomOverComp z q = LQ.one t := by
    let : Group (SchemeHomOver t fQ) := LQ.pointGroup t
    change NeronModelInfra.schemeHomOverComp (L.mul t x (L.inv t y)) q = 1
    rw [hq, Torsor.map_inv L LQ q hq, hxy]
    exact mul_inv_cancel _
  obtain ⟨n, hn⟩ := (hker t z).mp hz
  have hn1 : n.1 ≫ i = z.1 := congrArg Subtype.val hn
  let t' : pullback (i ≫ f) f ⟶ Spec (CommRingCat.of k) := pullback.snd (i ≫ f) f ≫ f
  let n' : SchemeHomOver t' (i ≫ f) := ⟨pullback.fst (i ≫ f) f, pullback.condition⟩
  let y' : SchemeHomOver t' f := ⟨pullback.snd (i ≫ f) f, rfl⟩
  let in' : SchemeHomOver t' f := NeronModelInfra.schemeHomOverComp n' (⟨i, rfl⟩ : SchemeHomOver (i
    ≫ f) f)
  have hin' : NeronModelInfra.schemeHomOverComp in' q = LQ.one t' := (hker t' in').mpr ⟨n', rfl⟩
  let w : SchemeHomOver t' f := L.mul t' in' y'
  have hw : w.1 ≫ q.1 = y'.1 ≫ q.1 := by
    have := hq t' in' y'
    rw [hin', LQ.one_mul] at this
    exact congrArg Subtype.val this
  let φ : pullback q.1 q.1 ⟶ pullback (i ≫ f) f :=
    pullback.lift n.1 (pullback.snd q.1 q.1) (by rw [n.2])
  let ψ : pullback (i ≫ f) f ⟶ pullback q.1 q.1 := pullback.lift w.1 y'.1 hw
  have hφ : φ ≫ t' = t := by change φ ≫ pullback.snd _ _ ≫ f = _; rw [pullback.lift_snd_assoc]
  have hψ : ψ ≫ t = t' := by change ψ ≫ pullback.snd _ _ ≫ f = _; rw [pullback.lift_snd_assoc]
  have hφin : GoodReductionJacobian.schemeHomOverComp φ hφ in' = z :=
    Subtype.ext (by simp only [GoodReductionJacobian.schemeHomOverComp_coe, in',
      NeronModelInfra.schemeHomOverComp_coe,
      n', φ, pullback.lift_fst_assoc, hn1])
  have hφy : GoodReductionJacobian.schemeHomOverComp φ hφ y' = y :=
    Subtype.ext (by simp only [GoodReductionJacobian.schemeHomOverComp_coe, y', y, φ,
      pullback.lift_snd])
  have hψx : GoodReductionJacobian.schemeHomOverComp ψ hψ x = w :=
    Subtype.ext (by simp only [GoodReductionJacobian.schemeHomOverComp_coe, x, ψ,
      pullback.lift_fst])
  have hψy : GoodReductionJacobian.schemeHomOverComp ψ hψ y = y' :=
    Subtype.ext (by simp only [GoodReductionJacobian.schemeHomOverComp_coe, y, y', ψ,
      pullback.lift_snd])
  refine ⟨⟨φ, ψ, ?_, ?_⟩, pullback.lift_snd _ _ _⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.id_comp]
      change φ ≫ ψ ≫ pullback.fst q.1 q.1 = x.1
      rw [pullback.lift_fst]
      have : GoodReductionJacobian.schemeHomOverComp φ hφ w = x := by
        change GoodReductionJacobian.schemeHomOverComp φ hφ (L.mul t' in' y') = x
        rw [L.mul_natural, hφin, hφy]
        change L.mul t (L.mul t x (L.inv t y)) y = x
        rw [L.mul_assoc, L.inv_mul_cancel, L.mul_one]
      exact congrArg Subtype.val this
    · rw [Category.assoc, Category.id_comp]
      show φ ≫ ψ ≫ pullback.snd q.1 q.1 = pullback.snd q.1 q.1
      rw [pullback.lift_snd, pullback.lift_snd]
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.id_comp]
      show ψ ≫ φ ≫ pullback.fst (i ≫ f) f = pullback.fst (i ≫ f) f
      rw [pullback.lift_fst, ← cancel_mono i, Category.assoc, hn1]
      have : GoodReductionJacobian.schemeHomOverComp ψ hψ z = in' := by
        change GoodReductionJacobian.schemeHomOverComp ψ hψ (L.mul t x (L.inv t y)) = in'
        rw [L.mul_natural, Torsor.inv_natural, hψx, hψy]
        change L.mul t' (L.mul t' in' y') (L.inv t' y') = in'
        rw [L.mul_assoc, L.mul_inv_cancel, L.mul_one]
      exact congrArg Subtype.val this
    · rw [Category.assoc, Category.id_comp]
      show ψ ≫ φ ≫ pullback.snd (i ≫ f) f = pullback.snd (i ≫ f) f
      rw [pullback.lift_snd, pullback.lift_snd]

end AbelianVarieties.NOSProofs.KernelTorsor
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOver_pullback_unit_equiv_ker.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.KernelPoints


universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_schemeNsmul_comp_eq_comp_schemeNsmul_of_hom

theorem _root_.GoodReductionJacobian.RelativeGroupLaw.exists_schemeHomOver_pullback_unit_equiv_ker
    {R : Type u} [CommRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (u : SchemeHomOver g f) :
    ∃ e : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        SchemeHomOver t (pullback.snd u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ≃
          {x : SchemeHomOver t g // NeronModelInfra.schemeHomOverComp x u = L.one t},
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (y : SchemeHomOver t (pullback.snd u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1)),
        ((e t y : {_x : SchemeHomOver t g // _}) : SchemeHomOver t g).1 =
          y.1 ≫ pullback.fst u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1 :=
  S17Glue.exists_schemeHomOver_pullback_unit_equiv_ker L u

end AbelianVarieties.NOSProofs.KernelPoints
end
