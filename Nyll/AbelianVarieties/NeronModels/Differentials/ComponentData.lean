/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Nyll.SchemeTheory.RingTheory.Differentials.TopForms
public import Nyll.SchemeTheory.LocalGeometry.SmoothnessDefect
public import Nyll.AbelianVarieties.NeronModels.WeakModel
public import Nyll.SchemeTheory.Modules.KaehlerDifferentials
public import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra

/-! # Differential orders along special-fibre components -/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_NeronModelInfra_OmegaMinimalComponentData.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace NeronModelInfra

attribute [local instance] AlgebraicGeometry.Scheme.Hom.kaehlerPresheafModule

section Reading

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K]
  {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K)) (d : ℕ) (ω : Γ(gK.topDifferentials d, ⊤))

/-- A smooth chart, a generic special-fibre component and the order of a generic top form. -/
structure ComponentReading where
  /-- The smooth chart. -/
  Y : Scheme.{u}
  /-- The structure morphism over the valuation ring. -/
  f : Y ⟶ Spec (CommRingCat.of R)
  /-- The chart is smooth over the valuation ring. -/
  smooth : Smooth f
  /-- The chart is locally of finite type. -/
  locallyOfFiniteType : LocallyOfFiniteType f
  /-- The comparison from the generic fibre to the given variety. -/
  e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK
  /-- The generic-fibre comparison is an open immersion. -/
  isOpenImmersion : IsOpenImmersion e.1
  /-- The generic point of the selected special-fibre component. -/
  y : Y
  /-- The selected point lies over the closed point. -/
  hy : f.base y = IsLocalRing.closedPoint R
  /-- The point is generic among special-fibre points specializing to it. -/
  hmax : ∀ y' : Y, y' ⤳ y → f.base y' = IsLocalRing.closedPoint R → y' = y
  /-- The local ring is a domain. -/
  isDomain : IsDomain (Y.presheaf.stalk y)
  /-- The local ring has its discrete valuation ring structure. -/
  isDiscreteValuationRing : IsDiscreteValuationRing (Y.presheaf.stalk y)
  /-- The base algebra on the local ring. -/
  algebra : Algebra R (Y.presheaf.stalk y)
  /-- The stalk algebra agrees with the chart structure morphism. -/
  halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))
  /-- The fraction field is an algebra over the generic base field. -/
  algebraK : Algebra K (FractionRing (Y.presheaf.stalk y))
  /-- The fraction-field algebras agree over the valuation ring. -/
  isScalarTower : IsScalarTower R K (FractionRing (Y.presheaf.stalk y))
  /-- A basis of local relative differentials. -/
  b : Module.Basis (Fin d) (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄R])
  /-- An affine neighborhood on the generic variety. -/
  U : XK.Opens
  /-- The neighborhood is affine. -/
  hU : IsAffineOpen U
  /-- The neighborhood maps to the fraction field of the component stalk. -/
  algebraU : Algebra Γ(XK, U) (FractionRing (Y.presheaf.stalk y))
  /-- The neighborhood algebra agrees with the generic base field. -/
  isScalarTowerU : let : Algebra K Γ(XK, U) := gK.sectionsAlgebra U
    IsScalarTower K Γ(XK, U) (FractionRing (Y.presheaf.stalk y))
  /-- The affine chart map gives the required generic point. -/
  hx : Spec.map (CommRingCat.ofHom
      (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))) ≫ hU.fromSpec =
    (schemeHomOverComp
      (pointGenericFibre (K := K) (K' := FractionRing (Y.presheaf.stalk y))
        (⟨Y.fromSpecStalk y, halg⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) f))
      e).1
  /-- The top-form representative on the affine neighborhood. -/
  ωU : ⋀[Γ(XK, U)]^d (gK.kaehlerPresheaf.obj (op U))
  /-- The representative restricts to the prescribed top form. -/
  hωU : gK.topToSections d U ωU = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω
  /-- The coefficient of the top form in the local differential basis. -/
  a : FractionRing (Y.presheaf.stalk y)
  /-- The coefficient computes the pullback of the generic top form. -/
  ha : let : Algebra K Γ(XK, U) := gK.sectionsAlgebra U
    TopFormOrder.topFormMap K K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)) d ωU =
      a • TopFormOrder.topFormMap R K (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)) d
        (exteriorPower.ιMulti (Y.presheaf.stalk y) d b)
  /-- The top-form coefficient is nonzero. -/
  ha0 : a ≠ 0

attribute [instance] ComponentReading.isOpenImmersion ComponentReading.isDomain
  ComponentReading.isDiscreteValuationRing

variable {R K gK d ω}

/-- The valuation of the top-form coefficient along this component. -/
def ComponentReading.n (T : ComponentReading R K gK d ω) : ℤ :=
  TopFormOrder.addOrd (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) T.a

end Reading

section Minimal

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K]
  {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K)) (d : ℕ) (ω : Γ(gK.topDifferentials d, ⊤))

/-- Finitely many inequivalent smooth charts representing special-fibre components. -/
structure MinimalComponentData where
  /-- The index set of chosen components. -/
  ι : Type u
  /-- There are finitely many chosen components. -/
  finite : Finite ι
  /-- At least one component is chosen. -/
  nonempty : Nonempty ι
  /-- The reading attached to each component. -/
  C : ι → ComponentReading R K gK d ω
  /-- Each chart is separated. -/
  isSeparated : ∀ c, IsSeparated (C c).f
  /-- Each chart is quasi-compact. -/
  quasiCompact : ∀ c, QuasiCompact (C c).f
  /-- Each chart has the prescribed generic fibre. -/
  isIso : ∀ c, IsIso (C c).e.1
  /-- Every special-fibre point specializes from the chosen generic point. -/
  hgen : ∀ c (y' : ↥(C c).Y), (C c).f.base y' = IsLocalRing.closedPoint R → (C c).y ⤳ y'
  /-- Distinct chosen charts do not admit a compatible local comparison. -/
  inequiv : ∀ c c', c ≠ c' → ∀ (U : ((C c).Y).Opens), (C c).y ∈ U →
    ∀ u : SchemeHomOver (U.ι ≫ (C c).f) (C c').f,
      (genericFibreRestrict R K (C c').f (U.ι ≫ (C c).f) u).1 ≫ (C c').e.1 ≠
        (genericFibreRestrict R K (C c).f (U.ι ≫ (C c).f) ⟨U.ι, rfl⟩).1 ≫ (C c).e.1

variable {R K gK d ω}

/-- All selected readings have minimal order, and every minimizer maps locally to one of them. -/
def MinimalComponentData.IsOmegaMinimal (D : MinimalComponentData R K gK d ω) : Prop :=
  (∀ (c : D.ι) (T : ComponentReading R K gK d ω), (D.C c).n ≤ T.n) ∧
  (∀ T : ComponentReading R K gK d ω, (∃ c : D.ι, T.n = (D.C c).n) →
    ∃ (c : D.ι) (W : T.Y.Opens) (hyW : T.y ∈ W) (ε : SchemeHomOver (W.ι ≫ T.f) (D.C c).f),
      IsOpenImmersion ε.1 ∧ ε.1.base ⟨T.y, hyW⟩ = (D.C c).y ∧
      (genericFibreRestrict R K (D.C c).f (W.ι ≫ T.f) ε).1 ≫ (D.C c).e.1 =
        (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1)

end Minimal

section Gates

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K]
  {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} {d : ℕ} {ω : Γ(gK.topDifferentials d, ⊤)}

theorem ComponentReading.n_eq_one_of_a_eq_uniformizer (T : ComponentReading R K gK d ω)
    (ϖ : T.Y.presheaf.stalk T.y)
    (hϖ : IsLocalRing.maximalIdeal (T.Y.presheaf.stalk T.y) = Ideal.span {ϖ})
    (h : T.a = algebraMap (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) ϖ) :
    T.n = 1 := by
  unfold ComponentReading.n
  rw [h]
  exact TopFormOrder.addOrd_uniformizer _ _ ϖ hϖ

theorem ComponentReading.n_eq_two_of_a_eq_uniformizer_sq (T : ComponentReading R K gK d ω)
    (ϖ : T.Y.presheaf.stalk T.y)
    (hϖ : IsLocalRing.maximalIdeal (T.Y.presheaf.stalk T.y) = Ideal.span {ϖ})
    (h : T.a = algebraMap (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) ϖ ^ 2) :
    T.n = 2 := by
  unfold ComponentReading.n
  rw [h]
  exact TopFormOrder.addOrd_uniformizer_sq _ _ ϖ hϖ

theorem MinimalComponentData.IsOmegaMinimal.n_eq (D : MinimalComponentData R K gK d ω)
    (hD : D.IsOmegaMinimal) (c c' : D.ι) : (D.C c).n = (D.C c').n :=
  le_antisymm (hD.1 c (D.C c')) (hD.1 c' (D.C c))

end Gates

end NeronModelInfra

end
end
