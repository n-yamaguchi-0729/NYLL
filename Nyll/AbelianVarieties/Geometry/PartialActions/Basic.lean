/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Nyll.AbelianVarieties.Geometry.GroupLaw
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.GeometricallyConnectedIdentityComponent
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.IrreducibleIdentityComponentIndex
public import Nyll.SchemeTheory.Morphisms.ReducedSmooth
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Partial actions and compatible open models

Define partial actions, extend fixed points over test schemes, and compare compatible model charts.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_GoodReductionJacobian_PartialAction.lean
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

namespace GoodReductionJacobian

/-- An action morphism defined on a dense open part of the product. -/
structure PartialAction (k : Type u) [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) where
  /-- The dense open domain of the action. -/
  dom : (pullback f p).Opens
  /-- The action domain is dense in the product. -/
  dense_dom : Dense (dom : Set ↥(pullback f p))
  /-- The action morphism on the domain. -/
  hom : (dom : Scheme.{u}) ⟶ P
  /-- The action respects the structure morphism. -/
  hom_comp : hom ≫ p = dom.ι ≫ pullback.snd f p ≫ p

namespace PartialAction

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)}

/-- Pair a group point with a point of the acted-on scheme. -/
abbrev pair {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
    (x : SchemeHomOver t p) : T ⟶ pullback f p :=
  pullback.lift γ.1 x.1 (γ.2.trans x.2.symm)

/-- The paired points lie in the open domain of the partial action. -/
def Defined (a : PartialAction k f p) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) : Prop :=
  Set.range (pair γ x) ⊆ (a.dom : Set ↥(pullback f p))

/-- Lift a pair of points to the domain on which the action is defined. -/
def liftDom (a : PartialAction k f p) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x) :
    T ⟶ (a.dom : Scheme.{u}) :=
  IsOpenImmersion.lift a.dom.ι (pair γ x) (by rw [Scheme.Opens.range_ι]; exact hd)

@[simp]
theorem liftDom_ι (a : PartialAction k f p) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x) :
    a.liftDom γ x hd ≫ a.dom.ι = pair γ x :=
  IsOpenImmersion.lift_fac _ _ _

theorem liftDom_hom_comp (a : PartialAction k f p) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f) (x : SchemeHomOver t p)
    (hd : a.Defined γ x) : (a.liftDom γ x hd ≫ a.hom) ≫ p = t := by
  rw [Category.assoc, a.hom_comp, ← Category.assoc (a.liftDom γ x hd), liftDom_ι,
    ← Category.assoc, pullback.lift_snd]
  exact x.2

/-- Apply the partial action to points lying in its domain. -/
def act (a : PartialAction k f p) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x) : SchemeHomOver t p :=
  ⟨a.liftDom γ x hd ≫ a.hom, a.liftDom_hom_comp γ x hd⟩

@[simp]
theorem act_coe (a : PartialAction k f p) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x) :
    (a.act γ x hd).1 = a.liftDom γ x hd ≫ a.hom :=
  rfl

/-- The unit fixes every point where its action is defined. -/
def UnitActs (a : PartialAction k f p) (L : RelativeGroupLaw k f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t p)
    (hd : a.Defined (L.one t) x), a.act (L.one t) x hd = x

/-- Two successive defined actions agree with multiplication of their group points. -/
def Assoc (a : PartialAction k f p) (L : RelativeGroupLaw k f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ δ : SchemeHomOver t f)
    (x : SchemeHomOver t p) (hd₁ : a.Defined δ x) (hd₂ : a.Defined γ (a.act δ x hd₁)),
    ∃ hd₃ : a.Defined (L.mul t γ δ) x, a.act γ (a.act δ x hd₁) hd₂ = a.act (L.mul t γ δ) x hd₃

/-- Map a point of an open model into the acted-on scheme. -/
def modelPoint {V : G.Opens} (ι : (V : Scheme.{u}) ⟶ P) (hι : ι ≫ p = V.ι ≫ f) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} (v : SchemeHomOver t (V.ι ≫ f)) : SchemeHomOver t p :=
  ⟨v.1 ≫ ι, by rw [Category.assoc, hι]; exact v.2⟩

@[simp]
theorem modelPoint_coe {V : G.Opens} (ι : (V : Scheme.{u}) ⟶ P) (hι : ι ≫ p = V.ι ≫ f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (v : SchemeHomOver t (V.ι ≫ f)) :
    (modelPoint ι hι v).1 = v.1 ≫ ι :=
  rfl

/-- The partial action agrees with multiplication on the chosen open model. -/
def Compatible (a : PartialAction k f p) (L : RelativeGroupLaw k f) (V : G.Opens)
    (ι : (V : Scheme.{u}) ⟶ P) (hι : ι ≫ p = V.ι ≫ f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f)
    (v w : SchemeHomOver t (V.ι ≫ f)),
    NeronModelInfra.schemeHomOverComp w (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) =
      L.mul t γ (NeronModelInfra.schemeHomOverComp v (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f)) →
    ∃ hd : a.Defined γ (modelPoint ι hι v), a.act γ (modelPoint ι hι v) hd = modelPoint ι hι w

/-- The action morphism does not extend to a strictly larger open domain. -/
def Maximal (a : PartialAction k f p) : Prop :=
  ∀ (U' : (pullback f p).Opens) (h' : (U' : Scheme.{u}) ⟶ P) (hle : a.dom ≤ U'),
    (pullback f p).homOfLE hle ≫ h' = a.hom → U' = a.dom

/-- A subset is preserved wherever the partial action is defined. -/
def Stable (a : PartialAction k f p) (W : Set ↥P) : Prop :=
  ∀ z : ↥(a.dom : Scheme.{u}), pullback.snd f p (a.dom.ι z) ∈ W → a.hom z ∈ W

end PartialAction

end GoodReductionJacobian

end

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_PartialAction_exists_defined_act_eq_of_forall_act_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.PartialActionFixedPoints


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open Topology

universe u

namespace GoodReductionJacobian
open _root_.GoodReductionJacobian
namespace PartialAction
open _root_.GoodReductionJacobian.PartialAction
namespace EverythingActs
open _root_.GoodReductionJacobian.PartialAction
open _root_.GoodReductionJacobian

section Law

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}

theorem inv_natural (L : RelativeGroupLaw k f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) =
      L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) :=
  L.inv_natural t t' ψ hψ x

end Law

section Group

variable {k : Type u} [Field k]

theorem irreducibleSpace_of_connectedSpace [IsAlgClosed k] {G : Scheme.{u}}
    (f : G ⟶ Spec (CommRingCat.of k)) [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f) : IrreducibleSpace G := by
  obtain ⟨G₀, i, L₀, hoi, -, hirr, hrange, -⟩ :=
    RelativeGroupLaw.exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
      k L
  have hsurj : Function.Surjective i := by
    rw [← Set.range_eq_univ, hrange]
    exact PreconnectedSpace.connectedComponent_eq_univ _
  exact hsurj.irreducibleSpace i.continuous

theorem isReduced_of_smooth {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k)) [Smooth f] :
    IsReduced G :=
  AlgebraicGeometry.isReduced_of_smooth_of_field f

end Group

section Main

variable {k : Type u} [Field k]

theorem main [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsSeparated p] [LocallyOfFiniteType p]
    (a : PartialAction k f p) (ha : a.Assoc L)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (he : a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀)
    (hfix : ∀ (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hd : a.Defined γ P₀),
      a.act γ P₀ hd = P₀)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f) :
    ∃ hd : a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀),
      a.act γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) hd =
        GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀ := by
  have : IrreducibleSpace G := irreducibleSpace_of_connectedSpace f L
  have : IsReduced G := isReduced_of_smooth f
  have : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨s, hs_fst, hs_snd⟩ : ∃ s : G ⟶ pullback f p,
      s ≫ pullback.fst f p = 𝟙 G ∧ s ≫ pullback.snd f p = f ≫ P₀.1 :=
    ⟨pullback.lift (𝟙 G) (f ≫ P₀.1)
        (by rw [Category.id_comp, Category.assoc, P₀.2, Category.comp_id]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hpair : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f),
      pair γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) = γ.1 ≫ s := by
    intro T t γ
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, hs_fst, Category.comp_id]
    · rw [pullback.lift_snd, Category.assoc, hs_snd, ← Category.assoc, γ.2]
      rfl
  set Ω : G.Opens := s ⁻¹ᵁ a.dom with hΩ_def
  have hDef : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f),
      a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) ↔
        ∀ z : T, γ.1 z ∈ Ω := by
    intro T t γ
    unfold Defined
    rw [hpair, Set.range_subset_iff]
    exact Iff.rfl
  have hP₀1 : GoodReductionJacobian.schemeHomOverComp (𝟙 (Spec (CommRingCat.of k)))
    (Category.comp_id _) P₀ = P₀ :=
    Subtype.ext (Category.id_comp _)
  have hDefk : ∀ γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, a.Defined γ P₀ ↔ γ.1
    (IsLocalRing.closedPoint k) ∈ Ω := by
    intro γ
    rw [← hP₀1, hDef]
    constructor
    · intro h; exact h (IsLocalRing.closedPoint k)
    · intro h z; rwa [Subsingleton.elim z (IsLocalRing.closedPoint k)]
  have heΩ : (L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k) ∈ Ω := (hDefk _).mp
    he
  have hkdef : ∀ γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, a.Defined γ P₀ := by
    intro γ
    let γG : SchemeHomOver f f := GoodReductionJacobian.schemeHomOverComp f (Category.comp_id f) γ
    let uG : SchemeHomOver f f := ⟨𝟙 G, Category.id_comp f⟩
    let ψ : G ⟶ G := (L.mul f γG (L.inv f uG)).1
    have hψ : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
        GoodReductionJacobian.schemeHomOverComp x.1 x.2 (L.mul f γG (L.inv f uG)) =
          L.mul (𝟙 (Spec (CommRingCat.of k))) γ (L.inv (𝟙 (Spec (CommRingCat.of k))) x) := by
      intro x
      have h1 : GoodReductionJacobian.schemeHomOverComp x.1 x.2 γG = γ := by
        apply Subtype.ext
        simp only [GoodReductionJacobian.schemeHomOverComp_coe, γG]
        rw [← Category.assoc, x.2, Category.id_comp]
      have h2 : GoodReductionJacobian.schemeHomOverComp x.1 x.2 uG = x :=
        Subtype.ext (Category.comp_id _)
      rw [L.mul_natural, inv_natural, h1, h2]
    have hψpt : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
        ψ (x.1 (IsLocalRing.closedPoint k)) = (L.mul (𝟙 (Spec (CommRingCat.of k))) γ (L.inv (𝟙 (Spec
          (CommRingCat.of k))) x)).1 (IsLocalRing.closedPoint k) := by
      intro x
      exact congrArg
        (fun φ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f =>
          φ.1.base (IsLocalRing.closedPoint k)) (hψ x)
    have hγe : L.mul (𝟙 (Spec (CommRingCat.of k))) γ (L.inv (𝟙 (Spec (CommRingCat.of k))) γ) = L.one
      (𝟙 (Spec (CommRingCat.of k))) := L.mul_inv_cancel _ _
    have hU : ((Ω ⊓ ψ ⁻¹ᵁ Ω : G.Opens) : Set G).Nonempty := by
      have h1 : (Ω : Set G).Nonempty := ⟨_, heΩ⟩
      have h2 : ((ψ ⁻¹ᵁ Ω : G.Opens) : Set G).Nonempty := by
        refine ⟨γ.1 (IsLocalRing.closedPoint k), ?_⟩
        change ψ (γ.1 (IsLocalRing.closedPoint k)) ∈ Ω
        rw [hψpt γ, hγe]
        exact heΩ
      exact nonempty_preirreducible_inter Ω.isOpen (ψ ⁻¹ᵁ Ω).isOpen h1 h2
    obtain ⟨x₀, hx₀U, hx₀c⟩ :=
      nonempty_inter_closedPoints hU (Ω ⊓ ψ ⁻¹ᵁ Ω).isOpen.isLocallyClosed
    let x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f :=
      ⟨pointOfClosedPoint f x₀ hx₀c, pointOfClosedPoint_comp f x₀ hx₀c⟩
    have hxpt : x.1 (IsLocalRing.closedPoint k) = x₀ := pointOfClosedPoint_apply f x₀ hx₀c
      (IsLocalRing.closedPoint k)
    have hxΩ : x.1 (IsLocalRing.closedPoint k) ∈ Ω := by rw [hxpt]; exact hx₀U.1
    have hδΩ : (L.mul (𝟙 (Spec (CommRingCat.of k))) γ (L.inv (𝟙 (Spec (CommRingCat.of k))) x)).1
      (IsLocalRing.closedPoint k) ∈ Ω := by
      rw [← hψpt x]
      have h : x₀ ∈ (ψ ⁻¹ᵁ Ω : G.Opens) := hx₀U.2
      rw [hxpt]
      exact h
    have hdx : a.Defined x P₀ := (hDefk x).mpr hxΩ
    have hdδ : a.Defined (L.mul (𝟙 (Spec (CommRingCat.of k))) γ (L.inv (𝟙 (Spec (CommRingCat.of k)))
      x)) P₀ := (hDefk _).mpr hδΩ
    have hfx : a.act x P₀ hdx = P₀ := hfix x hdx
    have hdδ' : a.Defined (L.mul (𝟙 (Spec (CommRingCat.of k))) γ (L.inv (𝟙 (Spec (CommRingCat.of
      k))) x)) (a.act x P₀ hdx) := by
      rw [hfx]; exact hdδ
    obtain ⟨hd3, -⟩ := ha (𝟙 (Spec (CommRingCat.of k))) (L.mul (𝟙 (Spec (CommRingCat.of k))) γ
      (L.inv (𝟙 (Spec (CommRingCat.of k))) x)) x P₀ hdx hdδ'
    have hγeq : L.mul (𝟙 (Spec (CommRingCat.of k))) (L.mul (𝟙 (Spec (CommRingCat.of k))) γ (L.inv (𝟙
      (Spec (CommRingCat.of k))) x)) x = γ := by
      rw [L.mul_assoc, L.inv_mul_cancel, L.mul_one]
    rwa [hγeq] at hd3
  have hΩ : ∀ g : G, g ∈ Ω := by
    intro g
    by_contra hg
    have hne : ((Ω : Set G)ᶜ).Nonempty := ⟨g, hg⟩
    obtain ⟨x₀, hx₀, hx₀c⟩ :=
      nonempty_inter_closedPoints hne Ω.isOpen.isClosed_compl.isLocallyClosed
    apply hx₀
    have h := (hDefk ⟨pointOfClosedPoint f x₀ hx₀c, pointOfClosedPoint_comp f x₀ hx₀c⟩).mp
      (hkdef _)
    have h' : (pointOfClosedPoint f x₀ hx₀c).base (IsLocalRing.closedPoint k) ∈ Ω := h
    exact pointOfClosedPoint_apply f x₀ hx₀c (IsLocalRing.closedPoint k) ▸ h'
  have hdT : a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) :=
    (hDef t γ).mpr (fun z => hΩ _)
  refine ⟨hdT, ?_⟩
  have hsr : Set.range s ⊆ Set.range a.dom.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨g, rfl⟩
    exact hΩ g
  let s' : G ⟶ (a.dom : Scheme.{u}) := IsOpenImmersion.lift a.dom.ι s hsr
  have hs' : s' ≫ a.dom.ι = s := IsOpenImmersion.lift_fac _ _ _
  let o : G ⟶ P := s' ≫ a.hom
  have ho_p : o ≫ p = f := by
    change (s' ≫ a.hom) ≫ p = f
    rw [Category.assoc, a.hom_comp, ← Category.assoc s', hs', ← Category.assoc, hs_snd,
      Category.assoc, P₀.2, Category.comp_id]
  have hc_p : (f ≫ P₀.1) ≫ p = f := by rw [Category.assoc, P₀.2, Category.comp_id]
  have hact : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f)
      (hd : a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀)),
      (a.act γ _ hd).1 = γ.1 ≫ o := by
    intro T t γ hd
    have hl : a.liftDom γ _ hd = γ.1 ≫ s' := by
      rw [← cancel_mono a.dom.ι, liftDom_ι, Category.assoc, hs', hpair]
    rw [act_coe, hl, Category.assoc]
  have hoc : o = f ≫ P₀.1 := by
    have : LocallyOfFiniteType (o ≫ p) := by rw [ho_p]; infer_instance
    refine ext_of_apply_eq p Set.univ isOpen_univ.isLocallyClosed dense_univ ?_ (by rw [ho_p, hc_p])
    intro g _ hgc
    let gk : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f :=
      ⟨pointOfClosedPoint f g hgc, pointOfClosedPoint_comp f g hgc⟩
    have hdg : a.Defined gk
        (GoodReductionJacobian.schemeHomOverComp (𝟙 (Spec (CommRingCat.of k))) (Category.comp_id _)
          P₀) := by
      rw [hP₀1]; exact hkdef gk
    have hfixg : a.act gk _ hdg =
        GoodReductionJacobian.schemeHomOverComp (𝟙 (Spec (CommRingCat.of k))) (Category.comp_id _)
          P₀ := by
      have key : ∀ (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p) (hQ : Q = P₀) (hd : a.Defined
        gk Q),
          a.act gk Q hd = Q := by
        intro Q hQ hd; subst hQ; exact hfix gk hd
      exact key _ hP₀1 hdg
    have h1 : gk.1 ≫ o = gk.1 ≫ f ≫ P₀.1 := by
      rw [← hact (𝟙 (Spec (CommRingCat.of k))) gk hdg, hfixg,
        GoodReductionJacobian.schemeHomOverComp_coe,
        ← Category.assoc, gk.2]
    have h2 := congrArg
      (fun φ : Spec (CommRingCat.of k) ⟶ P => φ.base (IsLocalRing.closedPoint k)) h1
    have hgk : gk.1.base (IsLocalRing.closedPoint k) = g :=
      pointOfClosedPoint_apply f g hgc (IsLocalRing.closedPoint k)
    exact (congrArg o.base hgk).symm.trans
      (h2.trans (congrArg (f ≫ P₀.1).base hgk))
  apply Subtype.ext
  rw [hact t γ hdT, hoc, ← Category.assoc, γ.2]
  rfl

end Main

end GoodReductionJacobian.PartialAction.EverythingActs

theorem _root_.GoodReductionJacobian.PartialAction.exists_defined_act_eq_of_forall_act_eq
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsSeparated p] [LocallyOfFiniteType p]
    (a : PartialAction k f p) (ha : a.Assoc L)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (he : a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀)
    (hfix : ∀ (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hd : a.Defined γ P₀),
      a.act γ P₀ hd = P₀)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f) :
    ∃ hd : a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀),
      a.act γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) hd =
        GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀ :=
  GoodReductionJacobian.PartialAction.EverythingActs.main f L p a ha P₀ he hfix t γ

end AbelianVarieties.NOSProofs.PartialActionFixedPoints
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_PartialAction_base_hom_eq_of_compatible_of_isIso_stalkMap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.PartialActionTransport


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

universe u

noncomputable section

namespace GoodReductionJacobian
open _root_.GoodReductionJacobian
namespace PartialAction
open _root_.GoodReductionJacobian.PartialAction
namespace OpTransport

section GroupLawAux

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  (L : RelativeGroupLaw k f)

theorem mul_val_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of k)} (e : t = t')
    (x y : SchemeHomOver t f) (x' y' : SchemeHomOver t' f) (hx : x.1 = x'.1) (hy : y.1 = y'.1) :
    (L.mul t x y).1 = (L.mul t' x' y').1 := by
  subst e
  obtain rfl : x = x' := Subtype.ext hx
  obtain rfl : y = y' := Subtype.ext hy
  rfl

theorem inv_val_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of k)} (e : t = t')
    (x : SchemeHomOver t f) (x' : SchemeHomOver t' f) (hx : x.1 = x'.1) :
    (L.inv t x).1 = (L.inv t' x').1 := by
  subst e
  obtain rfl : x = x' := Subtype.ext hx
  rfl

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) :=
  L.inv_natural t t' ψ hψ x

theorem inv_mul_cancel_left {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver
    t f) :
    L.mul t (L.inv t x) (L.mul t x y) = y := by
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul]

include L in
theorem geometricallyIrreducible [LocallyOfFiniteType f] [QuasiCompact f] [ConnectedSpace G] :
    GeometricallyIrreducible f := by
  obtain ⟨G₀, i, L₀, hoi, -, -, hgi, -, hrange, -⟩ :=
    RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent k L
  have hsurj : Function.Surjective i := by
    rw [← Set.range_eq_univ, hrange]
    exact PreconnectedSpace.connectedComponent_eq_univ _
  have : IsIso i :=
    (isIso_iff_isOpenImmersion_and_epi_base i).mpr ⟨hoi, (TopCat.epi_iff_surjective _).mpr hsurj⟩
  have : MorphismProperty.RespectsIso (@GeometricallyIrreducible.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIrreducible.{u} i f).mp hgi

end GroupLawAux

section Chart

variable {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f)
  {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
  {V : G.Opens} (j : (V : Scheme.{u}) ⟶ P) (hj : j ≫ p = V.ι ≫ f)
  (a : PartialAction k f p)

/-- Pull the group-product coordinates back to the open model. -/
abbrev GV : Scheme.{u} := pullback (pullback.snd f p) j

/-- The structure map of the pulled-back group-product chart. -/
abbrev tGV : GV f p j ⟶ Spec (CommRingCat.of k) :=
  (pullback.fst (pullback.snd f p) j ≫ pullback.fst f p) ≫ f

/-- The group coordinate on the pulled-back chart. -/
def γ₀ : SchemeHomOver (tGV f p j) f :=
  ⟨pullback.fst (pullback.snd f p) j ≫ pullback.fst f p, rfl⟩

include hj in
theorem vG₀_over : (pullback.snd (pullback.snd f p) j ≫ V.ι) ≫ f = tGV f p j := by
  have h1 : pullback.snd (pullback.snd f p) j ≫ j =
      pullback.fst (pullback.snd f p) j ≫ pullback.snd f p := pullback.condition.symm
  calc (pullback.snd (pullback.snd f p) j ≫ V.ι) ≫ f
      = pullback.snd (pullback.snd f p) j ≫ (V.ι ≫ f) := Category.assoc _ _ _
    _ = pullback.snd (pullback.snd f p) j ≫ (j ≫ p) := by rw [hj]
    _ = (pullback.snd (pullback.snd f p) j ≫ j) ≫ p := (Category.assoc _ _ _).symm
    _ = (pullback.fst (pullback.snd f p) j ≫ pullback.snd f p) ≫ p := by rw [h1]
    _ = pullback.fst (pullback.snd f p) j ≫ (pullback.fst f p ≫ f) := by
        rw [Category.assoc, ← pullback.condition]
    _ = tGV f p j := (Category.assoc _ _ _).symm

/-- The model coordinate regarded as a group point. -/
def vG₀ : SchemeHomOver (tGV f p j) f :=
  ⟨pullback.snd (pullback.snd f p) j ≫ V.ι, vG₀_over f p j hj⟩

/-- The model coordinate as a point of the open model. -/
def v₀ : SchemeHomOver (tGV f p j) (V.ι ≫ f) :=
  ⟨pullback.snd (pullback.snd f p) j, by rw [← Category.assoc]; exact vG₀_over f p j hj⟩

/-- Multiply the group and model coordinates. -/
def m₀ : SchemeHomOver (tGV f p j) f := L.mul _ (γ₀ f p j) (vG₀ f p j hj)

/-- The open part of the chart where the product lies in the model. -/
abbrev Wch : (GV f p j).Opens := (m₀ f L p j hj).1 ⁻¹ᵁ V

/-- The structure map of the open product chart. -/
abbrev tWch : ((Wch f L p j hj : (GV f p j).Opens) : Scheme.{u}) ⟶ Spec (CommRingCat.of k) :=
  (Wch f L p j hj).ι ≫ tGV f p j

/-- The group coordinate restricted to the open product chart. -/
def γW : SchemeHomOver (tWch f L p j hj) f := schemeHomOverComp (Wch f L p j hj).ι rfl (γ₀ f p j)
/-- The model coordinate restricted to the open product chart. -/
def vW : SchemeHomOver (tWch f L p j hj) (V.ι ≫ f) := schemeHomOverComp (Wch f L p j hj).ι rfl (v₀ f
    p j hj)
/-- The model group point restricted to the open product chart. -/
def vGW : SchemeHomOver (tWch f L p j hj) f := schemeHomOverComp (Wch f L p j hj).ι rfl (vG₀ f p j
    hj)

theorem range_Wι_m₀ : Set.range ((Wch f L p j hj).ι ≫ (m₀ f L p j hj).1) ⊆ Set.range V.ι := by
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact w.2

/-- Lift the product coordinate into the open model. -/
def wW : SchemeHomOver (tWch f L p j hj) (V.ι ≫ f) :=
  ⟨IsOpenImmersion.lift V.ι _ (range_Wι_m₀ f L p j hj), by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, (m₀ f L p j hj).2]⟩

theorem wW_ι : (wW f L p j hj).1 ≫ V.ι = (Wch f L p j hj).ι ≫ (m₀ f L p j hj).1 :=
  IsOpenImmersion.lift_fac _ _ _

theorem compat_hyp :
    NeronModelInfra.schemeHomOverComp (wW f L p j hj) (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) =
      L.mul _ (γW f L p j hj)
        (NeronModelInfra.schemeHomOverComp (vW f L p j hj) (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f))
          := by
  have e : NeronModelInfra.schemeHomOverComp (vW f L p j hj) (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f)
    f) =
      vGW f L p j hj :=
    Subtype.ext (by simp only [vW, vGW, v₀, vG₀, GoodReductionJacobian.schemeHomOverComp_coe,
      NeronModelInfra.schemeHomOverComp_coe, Category.assoc])
  rw [e]
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe, wW_ι]
  change _ = (L.mul _ (schemeHomOverComp _ rfl (γ₀ f p j)) (schemeHomOverComp _ rfl (vG₀ f p j
    hj))).1
  rw [← L.mul_natural]
  rfl

variable (hc : a.Compatible L V j hj)

include hc in
theorem definedW : a.Defined (γW f L p j hj) (modelPoint j hj (vW f L p j hj)) :=
  (hc _ _ _ _ (compat_hyp f L p j hj)).choose

include hc in
theorem actW : a.act _ _ (definedW f L p j hj a hc) = modelPoint j hj (wW f L p j hj) :=
  (hc _ _ _ _ (compat_hyp f L p j hj)).choose_spec

/-- Map the compatible product chart into the partial-action domain. -/
def θd : ((Wch f L p j hj : (GV f p j).Opens) : Scheme.{u}) ⟶ (a.dom : Scheme.{u}) :=
  a.liftDom _ _ (definedW f L p j hj a hc)

theorem θd_ι : θd f L p j hj a hc ≫ a.dom.ι = (Wch f L p j hj).ι ≫ pullback.fst _ _ := by
  change a.liftDom (γW f L p j hj) (modelPoint j hj (vW f L p j hj))
    (definedW f L p j hj a hc) ≫ a.dom.ι = _
  rw [liftDom_ι]
  apply pullback.hom_ext
  · erw [pullback.lift_fst]
    simp only [γW, γ₀, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]
  · erw [pullback.lift_snd]
    simp only [modelPoint_coe, vW, v₀, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]
    rw [pullback.condition]

theorem θd_hom : θd f L p j hj a hc ≫ a.hom = (wW f L p j hj).1 ≫ j := by
  have := congrArg Subtype.val (actW f L p j hj a hc)
  simp only [act_coe, modelPoint_coe] at this
  exact this

scoped instance [IsOpenImmersion j] : IsOpenImmersion (θd f L p j hj a hc) := by
  have : IsOpenImmersion (θd f L p j hj a hc ≫ a.dom.ι) := by
    rw [θd_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ a.dom.ι

/-- Pair the unit section with the open model inclusion. -/
def σX : (V : Scheme.{u}) ⟶ pullback f p :=
  pullback.lift (L.one (V.ι ≫ f)).1 j (by rw [(L.one (V.ι ≫ f)).2, hj])

/-- Lift the unit-section pair to the pulled-back chart. -/
def σ : (V : Scheme.{u}) ⟶ GV f p j :=
  pullback.lift (σX f L p j hj) (𝟙 _) (by
    rw [Category.id_comp]; exact pullback.lift_snd _ _ _)

theorem σ_m₀ : σ f L p j hj ≫ (m₀ f L p j hj).1 = V.ι := by
  have hfst : σ f L p j hj ≫ pullback.fst (pullback.snd f p) j = σX f L p j hj :=
    pullback.lift_fst _ _ _
  have hsnd : σ f L p j hj ≫ pullback.snd (pullback.snd f p) j = 𝟙 _ :=
    pullback.lift_snd _ _ _
  have hσG : σ f L p j hj ≫ (γ₀ f p j).1 = (L.one (V.ι ≫ f)).1 := by
    change σ f L p j hj ≫ (pullback.fst _ _ ≫ pullback.fst f p) = _
    rw [← Category.assoc, hfst]
    exact pullback.lift_fst _ _ _
  have hσV : σ f L p j hj ≫ (vG₀ f p j hj).1 = V.ι := by
    change σ f L p j hj ≫ (pullback.snd _ _ ≫ V.ι) = _
    rw [← Category.assoc, hsnd, Category.id_comp]
  have et : σ f L p j hj ≫ tGV f p j = V.ι ≫ f := by
    change σ f L p j hj ≫ ((γ₀ f p j).1 ≫ f) = _
    rw [← Category.assoc, hσG]
    exact (L.one (V.ι ≫ f)).2
  have h1 : (schemeHomOverComp (σ f L p j hj) rfl (m₀ f L p j hj)).1 =
      (L.mul _ (L.one (V.ι ≫ f)) (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f)).1 := by
    rw [m₀, L.mul_natural]
    exact mul_val_congr L et _ _ _ _ hσG hσV
  rw [L.one_mul] at h1
  exact h1

scoped instance [Nonempty (V : Scheme.{u})] : Nonempty ((Wch f L p j hj : (GV f p j).Opens) :
    Scheme.{u}) := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (V : Scheme.{u}))
  refine ⟨⟨σ f L p j hj v, ?_⟩⟩
  change (m₀ f L p j hj).1 (σ f L p j hj v) ∈ (V : Set G)
  rw [← Scheme.Hom.comp_apply, σ_m₀]
  exact v.2

end Chart

section Generic

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)}

theorem act_congr (a : PartialAction k f p) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {γ γ' : SchemeHomOver t f} {x x' : SchemeHomOver t p} (eγ : γ = γ') (ex : x = x')
    (hd : a.Defined γ x) (hd' : a.Defined γ' x') : a.act γ x hd = a.act γ' x' hd' := by
  subst eγ ex; rfl

theorem compatible_restrict (L : RelativeGroupLaw k f) (a : PartialAction k f p)
    {V V' : G.Opens} (hV' : V' ≤ V) (ι₀ : (V : Scheme.{u}) ⟶ P) (hι₀ : ι₀ ≫ p = V.ι ≫ f)
    (hc : a.Compatible L V ι₀ hι₀)
    (hj : (G.homOfLE hV' ≫ ι₀) ≫ p = V'.ι ≫ f) :
    a.Compatible L V' (G.homOfLE hV' ≫ ι₀) hj := by
  intro T t γ v w hvw
  let vV : SchemeHomOver t (V.ι ≫ f) := ⟨v.1 ≫ G.homOfLE hV', by
    rw [Category.assoc, ← Category.assoc (G.homOfLE hV'), Scheme.homOfLE_ι]; exact v.2⟩
  let wV : SchemeHomOver t (V.ι ≫ f) := ⟨w.1 ≫ G.homOfLE hV', by
    rw [Category.assoc, ← Category.assoc (G.homOfLE hV'), Scheme.homOfLE_ι]; exact w.2⟩
  have hvw' : NeronModelInfra.schemeHomOverComp wV (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) =
      L.mul t γ (NeronModelInfra.schemeHomOverComp vV (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f)) :=
        by
    have e1 : NeronModelInfra.schemeHomOverComp wV (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) =
        NeronModelInfra.schemeHomOverComp w (⟨V'.ι, rfl⟩ : SchemeHomOver (V'.ι ≫ f) f) :=
      Subtype.ext (by simp only [wV, NeronModelInfra.schemeHomOverComp_coe,
        Category.assoc, Scheme.homOfLE_ι])
    have e2 : NeronModelInfra.schemeHomOverComp vV (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) =
        NeronModelInfra.schemeHomOverComp v (⟨V'.ι, rfl⟩ : SchemeHomOver (V'.ι ≫ f) f) :=
      Subtype.ext (by simp only [vV, NeronModelInfra.schemeHomOverComp_coe,
        Category.assoc, Scheme.homOfLE_ι])
    rw [e1, e2]; exact hvw
  obtain ⟨hd, hact⟩ := hc t γ vV wV hvw'
  have ev : modelPoint ι₀ hι₀ vV = modelPoint (G.homOfLE hV' ≫ ι₀) hj v := Subtype.ext (by simp only
    [modelPoint_coe, vV, Category.assoc])
  have ew : modelPoint ι₀ hι₀ wV = modelPoint (G.homOfLE hV' ≫ ι₀) hj w := Subtype.ext (by simp only
    [modelPoint_coe, wV, Category.assoc])
  rw [ev] at hd
  refine ⟨hd, ?_⟩
  rw [← ew, ← hact]
  exact act_congr a rfl ev.symm _ _

theorem eq_of_comp_eq_of_isIso_restrict {T P'' : Scheme.{u}} (β : P'' ⟶ P) (W : P.Opens) [IsIso (β
    ∣_ W)]
    (m₁ m₂ : T ⟶ P'') (h : m₁ ≫ β = m₂ ≫ β) (hW : Set.range (m₁ ≫ β) ⊆ (W : Set P)) : m₁ = m₂ := by
  have h₁ : Set.range m₁ ⊆ Set.range (β ⁻¹ᵁ W).ι := by
    rintro _ ⟨t, rfl⟩; rw [Scheme.Opens.range_ι]
    change β (m₁ t) ∈ (W : Set P)
    rw [← Scheme.Hom.comp_apply]; exact hW ⟨t, rfl⟩
  have h₂ : Set.range m₂ ⊆ Set.range (β ⁻¹ᵁ W).ι := by
    rintro _ ⟨t, rfl⟩; rw [Scheme.Opens.range_ι]
    change β (m₂ t) ∈ (W : Set P)
    rw [← Scheme.Hom.comp_apply, ← h]; exact hW ⟨t, rfl⟩
  let n₁ := IsOpenImmersion.lift (β ⁻¹ᵁ W).ι m₁ h₁
  let n₂ := IsOpenImmersion.lift (β ⁻¹ᵁ W).ι m₂ h₂
  have hn₁ : n₁ ≫ (β ⁻¹ᵁ W).ι = m₁ := IsOpenImmersion.lift_fac _ _ _
  have hn₂ : n₂ ≫ (β ⁻¹ᵁ W).ι = m₂ := IsOpenImmersion.lift_fac _ _ _
  have : n₁ ≫ (β ∣_ W) = n₂ ≫ (β ∣_ W) := by
    rw [← cancel_mono W.ι, Category.assoc, Category.assoc, morphismRestrict_ι, ← Category.assoc,
      hn₁,
      ← Category.assoc, hn₂, h]
  rw [cancel_mono] at this
  rw [← hn₁, ← hn₂, this]

end Generic

end OpTransport
end PartialAction
end GoodReductionJacobian

end

open _root_.GoodReductionJacobian.PartialAction
open GoodReductionJacobian.PartialAction.OpTransport in
theorem _root_.GoodReductionJacobian.PartialAction.base_hom_eq_of_compatible_of_isIso_stalkMap
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsProper p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι₀ : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι₀]
    (hι₀ : ι₀ ≫ p = V.ι ≫ f)
    (a : PartialAction k f p) (hc : a.Compatible L V ι₀ hι₀)
    (w : P) (ζ : ↥(pullback f p)) (_hζ : ζ ∈ a.dom)
    (hζcl : closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure {w})
    {P'' : Scheme.{u}} (p'' : P'' ⟶ Spec (CommRingCat.of k)) [IsIntegral P''] [IsSeparated p'']
    [LocallyOfFiniteType p'']
    (β : P'' ⟶ P) (hβ : β ≫ p = p'') (W : P.Opens) [IsIso (β ∣_ W)]
    (U' : (pullback f p).Opens) (hU' : U' ≤ a.dom) (hζU' : ζ ∈ U')
    (α' : (U' : Scheme.{u}) ⟶ P'') (hα' : α' ≫ β = (pullback f p).homOfLE hU' ≫ a.hom)
    {P' : Scheme.{u}} [IsIntegral P'] (ν : P' ⟶ P'') [IsIso ((ν ≫ β) ∣_ W)]
    (V' : G.Opens) [Nonempty (V' : Scheme.{u})] (hV' : V' ≤ V)
    (hV'W : Set.range (G.homOfLE hV' ≫ ι₀).base ⊆ (W : Set P))
    (ι' : (V' : Scheme.{u}) ⟶ P') [IsOpenImmersion ι'] (hι'ι₀ : ι' ≫ ν ≫ β = G.homOfLE hV' ≫ ι₀)
    (hι' : ι' ≫ (ν ≫ β) ≫ p = V'.ι ≫ f)
    (a' : PartialAction k f ((ν ≫ β) ≫ p)) (hc' : a'.Compatible L V' ι' hι')
    (w' : P') (hπw' : (ν ≫ β).base w' = w) (_hiso : IsIso ((ν ≫ β).stalkMap w'))
    (ζ' : ↥(pullback f ((ν ≫ β) ≫ p))) (hζ' : ζ' ∈ a'.dom)
    (hζ'cl : closure ({ζ'} : Set ↥(pullback f ((ν ≫ β) ≫ p))) =
      (pullback.snd f ((ν ≫ β) ≫ p)).base ⁻¹' closure {w'}) :
    ν.base (a'.hom.base ⟨ζ', hζ'⟩) = α'.base ⟨ζ, hζU'⟩ := by
  obtain ⟨PiM, hPi₁, hPi₂⟩ : ∃ PiM : pullback f ((ν ≫ β) ≫ p) ⟶ pullback f p,
      PiM ≫ pullback.fst f p = pullback.fst _ _ ∧ PiM ≫ pullback.snd f p = pullback.snd _ _ ≫ (ν ≫
        β) :=
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ (ν ≫ β)) (by rw [pullback.condition]; simp
      only [Category.assoc]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have : GeometricallyIrreducible f := geometricallyIrreducible L
  have : IrreducibleSpace ↥(pullback f p) := inferInstance
  have : IrreducibleSpace ↥(pullback f ((ν ≫ β) ≫ p)) := inferInstance
  have hPiζ : PiM ζ' = ζ := by
    have hcl : closure ({PiM ζ'} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure {w} :=
      by
      apply subset_antisymm
      · apply closure_minimal _ ((isClosed_closure).preimage (pullback.snd f p).continuous)
        rintro _ rfl
        change (pullback.snd f p) (PiM ζ') ∈ closure {w}
        rw [← Scheme.Hom.comp_apply, hPi₂, Scheme.Hom.comp_apply, ← hπw']
        have h1 : (pullback.snd f ((ν ≫ β) ≫ p)) ζ' ∈ closure {w'} := by
          rw [← Set.mem_preimage, ← hζ'cl]; exact subset_closure rfl
        have h2 := image_closure_subset_closure_image (ν ≫ β).continuous ⟨_, h1, rfl⟩
        rwa [Set.image_singleton] at h2
      · intro x hx
        rw [mem_closure_iff]
        intro O hO hxO
        have hsO : IsOpen ((pullback.snd f p).base '' O) := (pullback.snd f p).isOpenMap O hO
        have hw : w ∈ (pullback.snd f p).base '' O := by
          have hx' : (pullback.snd f p) x ∈ closure {w} := hx
          rw [mem_closure_iff] at hx'
          obtain ⟨y, hy, hy'⟩ := hx' _ hsO ⟨x, hxO, rfl⟩
          rw [Set.mem_singleton_iff] at hy'
          rw [← hy']; exact hy
        obtain ⟨x₀, hx₀O, hx₀⟩ := hw
        obtain ⟨z₀, hz₀₁, hz₀₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd f p)
          (g := ν ≫ β) x₀ w'
          (by rw [hx₀]; exact hπw'.symm)
        have he : (pullbackLeftPullbackSndIso f p (ν ≫ β)).hom ≫ PiM = pullback.fst _ _ := by
          apply pullback.hom_ext
          · rw [Category.assoc, hPi₁, pullbackLeftPullbackSndIso_hom_fst]
          · rw [Category.assoc, hPi₂, ← Category.assoc, pullbackLeftPullbackSndIso_hom_snd,
            pullback.condition]
        have hz' : (pullbackLeftPullbackSndIso f p (ν ≫ β)).hom z₀ ∈ closure ({ζ'} : Set _) := by
          rw [hζ'cl, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullbackLeftPullbackSndIso_hom_snd,
            hz₀₂]
          exact subset_closure rfl
        rw [mem_closure_iff] at hz'
        obtain ⟨y, hy, hy'⟩ := hz' (PiM.base ⁻¹' O) (hO.preimage PiM.continuous) (by
          change PiM ((pullbackLeftPullbackSndIso f p (ν ≫ β)).hom z₀) ∈ O
          rw [← Scheme.Hom.comp_apply, he, hz₀₁]; exact hx₀O)
        rw [Set.mem_singleton_iff] at hy'
        rw [hy'] at hy
        exact ⟨_, hy, rfl⟩
    exact (inseparable_iff_closure_eq.mpr (hcl.trans hζcl.symm)).eq
  let D' : (pullback f ((ν ≫ β) ≫ p)).Opens := a'.dom ⊓ PiM ⁻¹ᵁ U'
  have hζ'D : ζ' ∈ D' := ⟨hζ', by change PiM ζ' ∈ (U' : Set _); rw [hPiζ]; exact hζU'⟩
  have : Nonempty (D' : Scheme.{u}) := ⟨⟨ζ', hζ'D⟩⟩
  have : IrreducibleSpace (D' : Scheme.{u}) := D'.ι.isOpenEmbedding.irreducibleSpace
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : (D' : Scheme.{u}) ⟶ (a'.dom : Scheme.{u}), e₁ ≫ a'.dom.ι = D'.ι :=
    ⟨(pullback f ((ν ≫ β) ≫ p)).homOfLE inf_le_left, Scheme.homOfLE_ι _ _⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : (D' : Scheme.{u}) ⟶ (U' : Scheme.{u}), lam ≫ U'.ι = D'.ι ≫ PiM :=
    ⟨IsOpenImmersion.lift U'.ι (D'.ι ≫ PiM) (by
      rintro _ ⟨d, rfl⟩; rw [Scheme.Opens.range_ι]; exact d.2.2), IsOpenImmersion.lift_fac _ _ _⟩
  let φ₁ : (D' : Scheme.{u}) ⟶ P'' := e₁ ≫ a'.hom ≫ ν
  let φ₂ : (D' : Scheme.{u}) ⟶ P'' := lam ≫ α'
  have hc1 : pullback.snd f ((ν ≫ β) ≫ p) ≫ (ν ≫ β) ≫ p = pullback.fst f ((ν ≫ β) ≫ p) ≫ f :=
    pullback.condition.symm
  have hc2 : pullback.snd f p ≫ p = pullback.fst f p ≫ f := pullback.condition.symm
  have hφ₁ : φ₁ ≫ p'' = D'.ι ≫ pullback.fst _ _ ≫ f := by
    have h3 : a'.hom ≫ ν ≫ β ≫ p = a'.dom.ι ≫ pullback.fst _ _ ≫ f := by
      rw [show ν ≫ β ≫ p = (ν ≫ β) ≫ p by simp only [Category.assoc], a'.hom_comp, hc1]
    simp only [φ₁, Category.assoc]
    rw [← hβ, h3, ← Category.assoc e₁, he₁]
  have hφ₂ : φ₂ ≫ p'' = D'.ι ≫ pullback.fst _ _ ≫ f := by
    simp only [φ₂, Category.assoc]
    calc lam ≫ α' ≫ p'' = lam ≫ α' ≫ β ≫ p := by rw [← hβ]
      _ = lam ≫ ((pullback f p).homOfLE hU' ≫ a.hom) ≫ p := by rw [← Category.assoc α', hα']
      _ = lam ≫ (pullback f p).homOfLE hU' ≫ a.dom.ι ≫ pullback.snd f p ≫ p := by
          rw [Category.assoc ((pullback f p).homOfLE hU') a.hom p, a.hom_comp]
      _ = lam ≫ U'.ι ≫ pullback.snd f p ≫ p := by
          rw [← Category.assoc ((pullback f p).homOfLE hU'), Scheme.homOfLE_ι]
      _ = (lam ≫ U'.ι) ≫ pullback.fst f p ≫ f := by rw [hc2]; exact (Category.assoc lam U'.ι _).symm
      _ = (D'.ι ≫ PiM) ≫ pullback.fst f p ≫ f := by rw [hlam]
      _ = D'.ι ≫ pullback.fst _ _ ≫ f := by
          rw [Category.assoc D'.ι PiM, ← Category.assoc PiM (pullback.fst f p) f, hPi₁]
  let ψ : (D' : Scheme.{u}) ⟶ pullback p'' p'' := pullback.lift φ₁ φ₂ (hφ₁.trans hφ₂.symm)
  have hS : IsClosed (ψ.base ⁻¹' Set.range (pullback.diagonal p'')) :=
    (pullback.diagonal p'').isClosedEmbedding.isClosed_range.preimage ψ.continuous
  let Wc := Wch f L ((ν ≫ β) ≫ p) ι' hι'
  let θ' := θd f L ((ν ≫ β) ≫ p) ι' hι' a' hc'
  have hθ'ι := θd_ι f L ((ν ≫ β) ≫ p) ι' hι' a' hc'
  have hθ'hom := θd_hom f L ((ν ≫ β) ≫ p) ι' hι' a' hc'
  have hjV : (G.homOfLE hV' ≫ ι₀) ≫ p = V'.ι ≫ f := by
    rw [Category.assoc, hι₀, ← Category.assoc, Scheme.homOfLE_ι]
  have hcV : a.Compatible L V' (G.homOfLE hV' ≫ ι₀) hjV := compatible_restrict L a hV' ι₀ hι₀ hc hjV
  obtain ⟨hd₂, hact₂⟩ := hcV (tWch f L ((ν ≫ β) ≫ p) ι' hι') (γW f L ((ν ≫ β) ≫ p) ι' hι') (vW f L
    ((ν ≫ β) ≫ p) ι' hι')
    (wW f L ((ν ≫ β) ≫ p) ι' hι') (compat_hyp f L ((ν ≫ β) ≫ p) ι' hι')
  let θ₂ := a.liftDom _ _ hd₂
  have hθ₂ι : θ₂ ≫ a.dom.ι = (Wc.ι ≫ pullback.fst _ _) ≫ PiM := by
    rw [liftDom_ι]
    apply pullback.hom_ext
    · erw [pullback.lift_fst]
      rw [Category.assoc _ PiM (pullback.fst f p), hPi₁]
      simp only [GoodReductionJacobian.PartialAction.OpTransport.γW,
        GoodReductionJacobian.PartialAction.OpTransport.γ₀,
        GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]
      rfl
    · erw [pullback.lift_snd]
      rw [Category.assoc _ PiM (pullback.snd f p), hPi₂, modelPoint_coe]
      simp only [GoodReductionJacobian.PartialAction.OpTransport.vW,
        GoodReductionJacobian.PartialAction.OpTransport.v₀,
        GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]
      rw [← hι'ι₀, pullback.condition_assoc]
  have hθ₂hom : θ₂ ≫ a.hom = (wW f L ((ν ≫ β) ≫ p) ι' hι').1 ≫ G.homOfLE hV' ≫ ι₀ := by
    have := congrArg Subtype.val hact₂
    simp only [act_coe, modelPoint_coe] at this
    exact this
  let W₀ : Wc.toScheme.Opens := ((Wc.ι ≫ pullback.fst _ _) ≫ PiM) ⁻¹ᵁ U'
  have hW₀ne : Nonempty (W₀ : Scheme.{u}) := by
    have h1 : IsOpen (Set.range (Wc.ι ≫ pullback.fst (pullback.snd f ((ν ≫ β) ≫ p)) ι').base) :=
      (Wc.ι ≫ pullback.fst _ _).isOpenEmbedding.isOpen_range
    have h2 : (Set.range (Wc.ι ≫ pullback.fst (pullback.snd f ((ν ≫ β) ≫ p)) ι').base).Nonempty :=
      Set.range_nonempty _
    have h3 : IsOpen (PiM.base ⁻¹' (U' : Set _)) := U'.2.preimage PiM.continuous
    have h4 : (PiM.base ⁻¹' (U' : Set _)).Nonempty := ⟨ζ', by
      change PiM ζ' ∈ (U' : Set _)
      rw [hPiζ]
      exact hζU'⟩
    obtain ⟨x, ⟨y, rfl⟩, hx2⟩ := nonempty_preirreducible_inter h1 h3 h2 h4
    exact ⟨⟨y, hx2⟩⟩
  obtain ⟨θD, hθD⟩ : ∃ θD : (W₀ : Scheme.{u}) ⟶ (D' : Scheme.{u}), θD ≫ D'.ι = W₀.ι ≫ Wc.ι ≫
    pullback.fst _ _ :=
    ⟨IsOpenImmersion.lift D'.ι (W₀.ι ≫ Wc.ι ≫ pullback.fst _ _) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      refine ⟨?_, ?_⟩
      · change (Wc.ι ≫ pullback.fst _ _) (W₀.ι x) ∈ (a'.dom : Set _)
        rw [← hθ'ι, Scheme.Hom.comp_apply]
        exact (θ' _).2
      · change PiM ((Wc.ι ≫ pullback.fst _ _) (W₀.ι x)) ∈ (U' : Set _)
        rw [← Scheme.Hom.comp_apply]
        exact x.2), IsOpenImmersion.lift_fac _ _ _⟩
  have : IsOpenImmersion θD := by
    have : IsOpenImmersion (θD ≫ D'.ι) := by rw [hθD]; infer_instance
    exact IsOpenImmersion.of_comp _ D'.ι
  have hE₁ : θD ≫ e₁ = W₀.ι ≫ θ' := by
    rw [← cancel_mono a'.dom.ι]
    simp only [Category.assoc]
    rw [he₁, hθD, hθ'ι]
  have hE₂ : θD ≫ lam ≫ (pullback f p).homOfLE hU' = W₀.ι ≫ θ₂ := by
    rw [← cancel_mono a.dom.ι]
    simp only [Category.assoc]
    rw [Scheme.homOfLE_ι, hlam, ← Category.assoc θD D'.ι PiM, hθD, hθ₂ι]
    simp only [Category.assoc]
  have l1 : (θD ≫ φ₁) ≫ β = W₀.ι ≫ (wW f L ((ν ≫ β) ≫ p) ι' hι').1 ≫ G.homOfLE hV' ≫ ι₀ := by
    simp only [φ₁, Category.assoc]
    rw [← Category.assoc θD e₁, hE₁, Category.assoc W₀.ι θ', ← Category.assoc θ' a'.hom, hθ'hom,
      Category.assoc (wW f L ((ν ≫ β) ≫ p) ι' hι').1 ι', hι'ι₀]
  have l2 : (θD ≫ φ₂) ≫ β = W₀.ι ≫ (wW f L ((ν ≫ β) ≫ p) ι' hι').1 ≫ G.homOfLE hV' ≫ ι₀ := by
    simp only [φ₂, Category.assoc]
    rw [hα', ← Category.assoc lam ((pullback f p).homOfLE hU') a.hom, ← Category.assoc θD (lam ≫ _)
      a.hom, hE₂,
      Category.assoc W₀.ι θ₂ a.hom, hθ₂hom]
  have hkey : θD ≫ φ₁ = θD ≫ φ₂ := by
    apply eq_of_comp_eq_of_isIso_restrict β W
    · rw [l1, l2]
    · rintro _ ⟨x, rfl⟩
      rw [l1, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact hV'W ⟨_, rfl⟩
  have hmor : (θD ≫ φ₁) ≫ pullback.diagonal p'' = θD ≫ ψ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
      erw [pullback.lift_fst]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
      erw [pullback.lift_snd]
      exact hkey
  have hsub : Set.range θD.base ⊆ ψ.base ⁻¹' Set.range (pullback.diagonal p'') := by
    rintro _ ⟨x, rfl⟩
    refine ⟨(θD ≫ φ₁) x, ?_⟩
    change (pullback.diagonal p'') ((θD ≫ φ₁) x) = ψ (θD x)
    rw [← Scheme.Hom.comp_apply, hmor, Scheme.Hom.comp_apply]
  have huniv : ψ.base ⁻¹' Set.range (pullback.diagonal p'') = Set.univ := by
    have hopen : IsOpen (Set.range θD.base) := θD.isOpenEmbedding.isOpen_range
    have hdense : Dense (Set.range θD.base) := hopen.dense (Set.range_nonempty _)
    apply Set.eq_univ_of_univ_subset
    rw [← hdense.closure_eq]
    exact hS.closure_subset_iff.mpr hsub
  have hz : (⟨ζ', hζ'D⟩ : ↥(D' : Scheme.{u})) ∈ ψ.base ⁻¹' Set.range (pullback.diagonal p'') := by
    rw [huniv]; trivial
  obtain ⟨d, hd⟩ := hz
  have h1 := congrArg (pullback.fst p'' p'').base hd
  have h2 := congrArg (pullback.snd p'' p'').base hd
  change (pullback.diagonal p'' ≫ pullback.fst p'' p'') d =
    (ψ ≫ pullback.fst p'' p'') ⟨ζ', hζ'D⟩ at h1
  change (pullback.diagonal p'' ≫ pullback.snd p'' p'') d =
    (ψ ≫ pullback.snd p'' p'') ⟨ζ', hζ'D⟩ at h2
  rw [pullback.diagonal_fst] at h1
  rw [pullback.diagonal_snd] at h2
  erw [pullback.lift_fst] at h1
  erw [pullback.lift_snd] at h2
  have hid : ∀ y : ↥P'', (𝟙 P'' : P'' ⟶ P'') y = y := fun y => by
    rw [Scheme.Hom.id_base]; rfl
  rw [hid] at h1 h2
  have hζ₁ : e₁ ⟨ζ', hζ'D⟩ = ⟨ζ', hζ'⟩ := by
    apply Subtype.ext
    change (e₁ ≫ a'.dom.ι) ⟨ζ', hζ'D⟩ = ζ'
    rw [he₁]; rfl
  have hζ₂ : lam ⟨ζ', hζ'D⟩ = ⟨ζ, hζU'⟩ := by
    apply Subtype.ext
    change (lam ≫ U'.ι) ⟨ζ', hζ'D⟩ = ζ
    rw [hlam]
    exact hPiζ
  have e₁' : φ₁ ⟨ζ', hζ'D⟩ = ν (a'.hom ⟨ζ', hζ'⟩) := by
    exact congrArg (fun z : ↥(a'.dom : Scheme.{u}) => ν.base (a'.hom.base z)) hζ₁
  have e₂' : φ₂ ⟨ζ', hζ'D⟩ = α' ⟨ζ, hζU'⟩ := by
    exact congrArg α'.base hζ₂
  change ν (a'.hom ⟨ζ', hζ'⟩) = α' ⟨ζ, hζU'⟩
  rw [← e₁', ← e₂', ← h1, ← h2]

end AbelianVarieties.NOSProofs.PartialActionTransport
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_PartialAction_closure_image_preimage_closure_eq_closure_singleton.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.PartialActionSpecialization


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Topology

universe u

theorem
    _root_.GoodReductionJacobian.PartialAction.closure_image_preimage_closure_eq_closure_singleton
    {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)} (a : PartialAction k f p)
    (Z : Set ↥P) (ζ : ↥(pullback f p)) (hζ : ζ ∈ a.dom)
    (hζcl : closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure Z) :
    closure (a.hom.base '' ((a.dom.ι ≫ pullback.snd f p).base ⁻¹' closure Z)) =
      closure ({a.hom.base ⟨ζ, hζ⟩} : Set ↥P) := by
  let ζd : ↥(a.dom : Scheme.{u}) := ⟨ζ, hζ⟩
  change closure (a.hom.base '' ((a.dom.ι ≫ pullback.snd f p).base ⁻¹' closure Z)) =
    closure ({a.hom.base ζd} : Set ↥P)
  have himg : a.dom.ι.base '' ({ζd} : Set ↥(a.dom : Scheme.{u})) = {ζ} := by
    rw [Set.image_singleton]
    rfl
  have hpre : (a.dom.ι ≫ pullback.snd f p).base ⁻¹' closure Z =
      closure ({ζd} : Set ↥(a.dom : Scheme.{u})) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, ← hζcl,
      a.dom.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image]
    congr 2
    exact himg.symm
  rw [hpre]
  apply le_antisymm
  · have hmap : a.hom.base '' closure ({ζd} : Set ↥(a.dom : Scheme.{u})) ⊆
        closure ({a.hom.base ζd} : Set ↥P) := by
      simpa only [Set.image_singleton] using
        (image_closure_subset_closure_image a.hom.base.hom.continuous
          (s := ({ζd} : Set ↥(a.dom : Scheme.{u}))))
    exact closure_minimal hmap isClosed_closure
  · exact closure_mono (Set.singleton_subset_iff.2 ⟨_, subset_closure rfl, rfl⟩)

end AbelianVarieties.NOSProofs.PartialActionSpecialization
end
