/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Nyll.AbelianVarieties.NeronModels.Endomorphisms
public import Nyll.SchemeTheory.BaseChange.SchemeHomOver
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Restriction of Néron endomorphisms to the special fibre

Extend generic endomorphisms by the Néron mapping property and restrict to a closed fibre.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_NeronSpecialFibreRestriction.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace NeronSpecialFibreInfra

section RelativeHomBookkeeping

variable {B X Y Z : Scheme.{u}}

/-- The identity morphism over the base, using the shared relative-morphism construction. -/
def homOverId (f : X ⟶ B) : SchemeHomOver f f :=
  NeronModelInfra.schemeHomOverId f

@[simp]
theorem homOverId_coe (f : X ⟶ B) : (homOverId f).1 = 𝟙 X :=
  rfl

/-- Composition over the base, using the shared relative-morphism construction. -/
def homOverComp {e : Z ⟶ B} {g : Y ⟶ B} {f : X ⟶ B}
    (ψ : SchemeHomOver e g) (φ : SchemeHomOver g f) : SchemeHomOver e f :=
  NeronModelInfra.schemeHomOverComp ψ φ

@[simp]
theorem homOverComp_coe {e : Z ⟶ B} {g : Y ⟶ B} {f : X ⟶ B}
    (ψ : SchemeHomOver e g) (φ : SchemeHomOver g f) :
    (homOverComp ψ φ).1 = ψ.1 ≫ φ.1 :=
  rfl

end RelativeHomBookkeeping

section FibreRestrictAlong

variable {B C X Y Z : Scheme.{u}}

/-- Restrict a relative morphism along a change of base. -/
def fibreRestrictAlong (c : C ⟶ B) (f : X ⟶ B) (g : Y ⟶ B) (φ : SchemeHomOver g f) :
    SchemeHomOver (pullback.snd g c) (pullback.snd f c) :=
  NeronModelInfra.fibreRestrictAlong c f g φ

@[reassoc (attr := simp)]
theorem fibreRestrictAlong_coe_comp_fst (c : C ⟶ B) (f : X ⟶ B) (g : Y ⟶ B)
    (φ : SchemeHomOver g f) :
    (fibreRestrictAlong c f g φ).1 ≫ pullback.fst f c = pullback.fst g c ≫ φ.1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fibreRestrictAlong_coe_comp_snd (c : C ⟶ B) (f : X ⟶ B) (g : Y ⟶ B)
    (φ : SchemeHomOver g f) :
    (fibreRestrictAlong c f g φ).1 ≫ pullback.snd f c = pullback.snd g c :=
  pullback.lift_snd _ _ _

theorem fibreRestrictAlong_coe_eq_pullbackMap (c : C ⟶ B) (f : X ⟶ B) (g : Y ⟶ B)
    (φ : SchemeHomOver g f)
    (eq₁ : g ≫ 𝟙 B = φ.1 ≫ f) (eq₂ : c ≫ 𝟙 B = 𝟙 C ≫ c) :
    (fibreRestrictAlong c f g φ).1 =
      pullback.map g c f c φ.1 (𝟙 C) (𝟙 B) eq₁ eq₂ :=
  NeronModelInfra.fibreRestrictAlong_coe_eq_pullbackMap c f g φ eq₁ eq₂

theorem fibreRestrictAlong_homOverId (c : C ⟶ B) (f : X ⟶ B) :
    fibreRestrictAlong c f f (homOverId f) = homOverId (pullback.snd f c) :=
  NeronModelInfra.fibreRestrictAlong_schemeHomOverId c f

theorem fibreRestrictAlong_homOverComp (c : C ⟶ B) (f : X ⟶ B) (g : Y ⟶ B) (e : Z ⟶ B)
    (ψ : SchemeHomOver e g) (φ : SchemeHomOver g f) :
    fibreRestrictAlong c f e (homOverComp ψ φ) =
      homOverComp (fibreRestrictAlong c g e ψ) (fibreRestrictAlong c f g φ) :=
  NeronModelInfra.fibreRestrictAlong_schemeHomOverComp c f g e ψ φ

end FibreRestrictAlong

section GenericFibreComparison

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
variable {X Y Z : Scheme.{u}}

theorem fibreRestrictAlong_specGenericFibreInclusion
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (φ : SchemeHomOver g f) :
    fibreRestrictAlong (specGenericFibreInclusion R K) f g φ =
      genericFibreRestrict R K f g φ :=
  rfl

theorem genericFibreRestrict_homOverId (f : X ⟶ Spec (CommRingCat.of R)) :
    genericFibreRestrict R K f f (homOverId f) =
      homOverId (pullback.snd f (specGenericFibreInclusion R K)) :=
  fibreRestrictAlong_homOverId (specGenericFibreInclusion R K) f

theorem genericFibreRestrict_homOverComp (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R)) (e : Z ⟶ Spec (CommRingCat.of R))
    (ψ : SchemeHomOver e g) (φ : SchemeHomOver g f) :
    genericFibreRestrict R K f e (homOverComp ψ φ) =
      homOverComp (genericFibreRestrict R K g e ψ) (genericFibreRestrict R K f g φ) :=
  fibreRestrictAlong_homOverComp (specGenericFibreInclusion R K) f g e ψ φ

end GenericFibreComparison

section SpecialFibre

variable (R : Type u) [CommRing R] (m : Ideal R)
variable {X Y Z : Scheme.{u}}

/-- The inclusion of the fibre over the quotient by an ideal. -/
def specClosedFibreInclusion : Spec (CommRingCat.of (R ⧸ m)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m))

@[simp]
theorem specClosedFibreInclusion_eq :
    specClosedFibreInclusion R m = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) :=
  rfl

theorem specClosedFibreInclusion_eq_spec_algebraMap :
    specClosedFibreInclusion R m =
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ m))) := by
  simp only [specClosedFibreInclusion_eq, Ideal.Quotient.algebraMap_eq]

theorem isClosedImmersion_specClosedFibreInclusion :
    IsClosedImmersion (specClosedFibreInclusion R m) :=
  IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk m)) Ideal.Quotient.mk_surjective

theorem isField_residueField [m.IsMaximal] : IsField (R ⧸ m) :=
  (Ideal.Quotient.maximal_ideal_iff_isField_quotient m).mp inferInstance

/-- Restrict a relative morphism to the fibre over the quotient by an ideal. -/
def specialFibreRestrict (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (φ : SchemeHomOver g f) :
    SchemeHomOver (pullback.snd g (specClosedFibreInclusion R m))
      (pullback.snd f (specClosedFibreInclusion R m)) :=
  fibreRestrictAlong (specClosedFibreInclusion R m) f g φ

theorem specialFibreRestrict_eq_fibreRestrictAlong
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (φ : SchemeHomOver g f) :
    specialFibreRestrict R m f g φ =
      fibreRestrictAlong (specClosedFibreInclusion R m) f g φ :=
  rfl

@[reassoc (attr := simp)]
theorem specialFibreRestrict_coe_comp_fst (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R)) (φ : SchemeHomOver g f) :
    (specialFibreRestrict R m f g φ).1 ≫ pullback.fst f (specClosedFibreInclusion R m) =
      pullback.fst g (specClosedFibreInclusion R m) ≫ φ.1 :=
  fibreRestrictAlong_coe_comp_fst (specClosedFibreInclusion R m) f g φ

@[reassoc (attr := simp)]
theorem specialFibreRestrict_coe_comp_snd (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R)) (φ : SchemeHomOver g f) :
    (specialFibreRestrict R m f g φ).1 ≫ pullback.snd f (specClosedFibreInclusion R m) =
      pullback.snd g (specClosedFibreInclusion R m) :=
  fibreRestrictAlong_coe_comp_snd (specClosedFibreInclusion R m) f g φ

theorem specialFibreRestrict_homOverId (f : X ⟶ Spec (CommRingCat.of R)) :
    specialFibreRestrict R m f f (homOverId f) =
      homOverId (pullback.snd f (specClosedFibreInclusion R m)) :=
  fibreRestrictAlong_homOverId (specClosedFibreInclusion R m) f

theorem specialFibreRestrict_homOverComp (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R)) (e : Z ⟶ Spec (CommRingCat.of R))
    (ψ : SchemeHomOver e g) (φ : SchemeHomOver g f) :
    specialFibreRestrict R m f e (homOverComp ψ φ) =
      homOverComp (specialFibreRestrict R m g e ψ) (specialFibreRestrict R m f g φ) :=
  fibreRestrictAlong_homOverComp (specClosedFibreInclusion R m) f g e ψ φ

end SpecialFibre

section NeronEndExtension

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable [IsDedekindDomain R] [IsFractionRing R K]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- The generic-fibre restriction equivalence supplied by the Néron mapping property. -/
def neronEndRestrictEquiv (h : NeronModelPropertyBundle R K f) :
    SchemeHomOver f f ≃
      SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
        (pullback.snd f (specGenericFibreInclusion R K)) :=
  h.endExtensionEquiv

@[simp]
theorem neronEndRestrictEquiv_apply (h : NeronModelPropertyBundle R K f)
    (Φ : SchemeHomOver f f) :
    neronEndRestrictEquiv h Φ = genericFibreRestrict R K f f Φ :=
  rfl

/-- The unique model endomorphism extending a generic endomorphism. -/
def neronEndExtension (h : NeronModelPropertyBundle R K f)
    (v : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    SchemeHomOver f f :=
  (neronEndRestrictEquiv h).symm v

@[simp]
theorem genericFibreRestrict_neronEndExtension (h : NeronModelPropertyBundle R K f)
    (v : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    genericFibreRestrict R K f f (neronEndExtension h v) = v :=
  h.restrict_endExtensionEquiv_symm v

theorem neronEndExtension_eq_of_restrict (h : NeronModelPropertyBundle R K f)
    {Φ : SchemeHomOver f f}
    {v : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))}
    (hΦ : genericFibreRestrict R K f f Φ = v) :
    neronEndExtension h v = Φ := by
  refine (h.neronMapping X f h.smooth).injective ?_
  rw [genericFibreRestrict_neronEndExtension, hΦ]

@[simp]
theorem neronEndExtension_genericFibreRestrict (h : NeronModelPropertyBundle R K f)
    (Φ : SchemeHomOver f f) :
    neronEndExtension h (genericFibreRestrict R K f f Φ) = Φ :=
  neronEndExtension_eq_of_restrict h rfl

theorem neronEndExtension_homOverId (h : NeronModelPropertyBundle R K f) :
    neronEndExtension h (homOverId (pullback.snd f (specGenericFibreInclusion R K))) =
      homOverId f :=
  neronEndExtension_eq_of_restrict h (genericFibreRestrict_homOverId R K f)

theorem neronEndExtension_homOverComp (h : NeronModelPropertyBundle R K f)
    (v w : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    neronEndExtension h (homOverComp v w) =
      homOverComp (neronEndExtension h v) (neronEndExtension h w) := by
  apply neronEndExtension_eq_of_restrict h
  simp only [genericFibreRestrict_homOverComp, genericFibreRestrict_neronEndExtension]

end NeronEndExtension

section NeronSpecialFibreTransfer

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable [IsDedekindDomain R] [IsFractionRing R K]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- Extend a generic endomorphism and restrict it to a closed fibre. -/
def neronSpecialFibreTransfer (h : NeronModelPropertyBundle R K f)
    (m : Ideal R) [m.IsMaximal]
    (v : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    SchemeHomOver (pullback.snd f (specClosedFibreInclusion R m))
      (pullback.snd f (specClosedFibreInclusion R m)) :=
  specialFibreRestrict R m f f (neronEndExtension h v)

theorem neronSpecialFibreTransfer_eq_of_restrict (h : NeronModelPropertyBundle R K f)
    (m : Ideal R) [m.IsMaximal] {Φ : SchemeHomOver f f}
    {v : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))}
    (hΦ : genericFibreRestrict R K f f Φ = v) :
    neronSpecialFibreTransfer h m v = specialFibreRestrict R m f f Φ :=
  congrArg (specialFibreRestrict R m f f) (neronEndExtension_eq_of_restrict h hΦ)

theorem specialFibreRestrict_congr_genericFibre (h : NeronModelPropertyBundle R K f)
    (m : Ideal R) [m.IsMaximal] {Φ Ψ : SchemeHomOver f f}
    (hΦΨ : genericFibreRestrict R K f f Φ = genericFibreRestrict R K f f Ψ) :
    specialFibreRestrict R m f f Φ = specialFibreRestrict R m f f Ψ :=
  congrArg (specialFibreRestrict R m f f) ((h.neronMapping X f h.smooth).injective hΦΨ)

theorem exists_neronExtension_specialFibreRestrict (h : NeronModelPropertyBundle R K f)
    (m : Ideal R) [m.IsMaximal]
    (v : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃ Φ : SchemeHomOver f f, genericFibreRestrict R K f f Φ = v ∧
      specialFibreRestrict R m f f Φ = neronSpecialFibreTransfer h m v :=
  ⟨neronEndExtension h v, genericFibreRestrict_neronEndExtension h v, rfl⟩

theorem neronSpecialFibreTransfer_homOverId (h : NeronModelPropertyBundle R K f)
    (m : Ideal R) [m.IsMaximal] :
    neronSpecialFibreTransfer h m
        (homOverId (pullback.snd f (specGenericFibreInclusion R K))) =
      homOverId (pullback.snd f (specClosedFibreInclusion R m)) :=
  (congrArg (specialFibreRestrict R m f f) (neronEndExtension_homOverId h)).trans
    (specialFibreRestrict_homOverId R m f)

theorem neronSpecialFibreTransfer_homOverComp (h : NeronModelPropertyBundle R K f)
    (m : Ideal R) [m.IsMaximal]
    (v w : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    neronSpecialFibreTransfer h m (homOverComp v w) =
      homOverComp (neronSpecialFibreTransfer h m v) (neronSpecialFibreTransfer h m w) :=
  (congrArg (specialFibreRestrict R m f f) (neronEndExtension_homOverComp h v w)).trans
    (specialFibreRestrict_homOverComp R m f f f
      (neronEndExtension h v) (neronEndExtension h w))

end NeronSpecialFibreTransfer

end NeronSpecialFibreInfra

end

end
