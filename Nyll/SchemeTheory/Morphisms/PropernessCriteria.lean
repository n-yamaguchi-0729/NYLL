/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.NoetherianSpace
public import Nyll.SchemeTheory.RingTheory.Localization.LocalAlgebraCriteria
public import Nyll.SchemeTheory.Morphisms.ProperBirationalSeparated
public import Nyll.SchemeTheory.Fibers.ClosedPointConnected
public import Nyll.SchemeTheory.Morphisms.ProperGlobalSectionsFinite
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.AdicCompletionLocalRing
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.AdicCompletionNoetherian

/-!
# Properness over local bases

Valuative bounds on sections, lifting clopen components over complete local rings, and
properness detected by a geometrically connected closed fiber with a section.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.Properness.ValuativeBounds

noncomputable section

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Filter

universe u v

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace ProperBounded
open _root_.AlgebraicGeometry

section Eval

variable {X : Scheme.{u}}

/-- Evaluate a section along a point whose image lies in the chosen open. -/
def evalHom {L : Type u} [CommRing L] (a : Spec (CommRingCat.of L) ⟶ X) (V : X.Opens) (h : ⊤ ≤ a ⁻¹ᵁ
    V) :
    Γ(X, V) →+* L :=
  (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom.comp (a.appLE V ⊤ h).hom

theorem ofHom_evalHom {L : Type u} [CommRing L] (a : Spec (CommRingCat.of L) ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ a ⁻¹ᵁ V) :
    CommRingCat.ofHom (evalHom a V h) = a.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom :=
  rfl

theorem evalHom_apply {L : Type u} [CommRing L] (a : Spec (CommRingCat.of L) ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ a ⁻¹ᵁ V) (g : Γ(X, V)) :
    evalHom a V h g = (Scheme.ΓSpecIso (CommRingCat.of L)).hom (a.appLE V ⊤ h g) :=
  rfl

theorem evalHom_map {L : Type u} [CommRing L] (a : Spec (CommRingCat.of L) ⟶ X) {V V' : X.Opens}
    (h : ⊤ ≤ a ⁻¹ᵁ V) (h' : ⊤ ≤ a ⁻¹ᵁ V') (i : V' ≤ V) (g : Γ(X, V)) :
    evalHom a V' h' (X.presheaf.map (homOfLE i).op g) = evalHom a V h g := by
  change (Scheme.ΓSpecIso (CommRingCat.of L)).hom ((X.presheaf.map (homOfLE i).op ≫ a.appLE V' ⊤ h')
    g) = _
  rw [Scheme.Hom.map_appLE]
  rfl

theorem evalHom_specMap_comp {L L' : Type u} [CommRing L] [CommRing L'] (φ : L →+* L')
    (b : Spec (CommRingCat.of L) ⟶ X) (V : X.Opens) (hb : ⊤ ≤ b ⁻¹ᵁ V)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ b) ⁻¹ᵁ V) :
    evalHom (Spec.map (CommRingCat.ofHom φ) ≫ b) V h = φ.comp (evalHom b V hb) := by
  have h1 : b.appLE V ⊤ hb ≫ (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_top =
      (Spec.map (CommRingCat.ofHom φ) ≫ b).appLE V ⊤ h :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have h2 : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_top = (Spec.map (CommRingCat.ofHom
    φ)).appTop :=
    Scheme.Hom.appLE_eq_app _
  have h3 : CommRingCat.ofHom (evalHom (Spec.map (CommRingCat.ofHom φ) ≫ b) V h) =
      CommRingCat.ofHom (φ.comp (evalHom b V hb)) := by
    rw [ofHom_evalHom, ← h1, h2, Category.assoc, Scheme.ΓSpecIso_naturality, CommRingCat.ofHom_comp,
      ofHom_evalHom, Category.assoc]
  exact congrArg CommRingCat.Hom.hom h3

theorem top_le_preimage_iff {L : Type u} [Field L] (a : Spec (CommRingCat.of L) ⟶ X) (V : X.Opens) :
    ⊤ ≤ a ⁻¹ᵁ V ↔ a.base default ∈ V := by
  constructor
  · intro h; exact h (Set.mem_univ (default : ↥(Spec (CommRingCat.of L))))
  · rintro h x -
    rw [Subsingleton.elim x default]
    exact h

theorem primeSpectrum_basicOpen_eq_top_iff {L : Type u} [Field L] (r : L) :
    PrimeSpectrum.basicOpen r = ⊤ ↔ r ≠ 0 := by
  constructor
  · intro h
    have hm : (default : PrimeSpectrum L) ∈ PrimeSpectrum.basicOpen r := by rw [h]; trivial
    rw [PrimeSpectrum.mem_basicOpen] at hm
    intro hr
    exact hm (hr ▸ Ideal.zero_mem _)
  · intro hr
    refine le_antisymm le_top ?_
    rw [← PrimeSpectrum.basicOpen_one, ← mul_inv_cancel₀ hr, PrimeSpectrum.basicOpen_mul]
    exact inf_le_left

theorem top_le_preimage_basicOpen_iff {L : Type u} [Field L] (a : Spec (CommRingCat.of L) ⟶ X) {V :
    X.Opens}
    (h : ⊤ ≤ a ⁻¹ᵁ V) (e : Γ(X, V)) :
    ⊤ ≤ a ⁻¹ᵁ X.basicOpen e ↔ evalHom a V h e ≠ 0 := by
  have h1 : (Spec (CommRingCat.of L)).basicOpen (a.appLE V ⊤ h e) = a ⁻¹ᵁ X.basicOpen e := by
    rw [Scheme.preimage_basicOpen, Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res]
    exact top_inf_eq _
  rw [← h1]
  change (⊤ : TopologicalSpace.Opens (PrimeSpectrum L)) ≤
    (Spec (CommRingCat.of L)).basicOpen (a.appLE V ⊤ h e) ↔ evalHom a V h e ≠ 0
  rw [basicOpen_eq_of_affine', top_le_iff]
  exact primeSpectrum_basicOpen_eq_top_iff _

theorem exists_eval_mul_pow_eq {V V' : X.Opens} (hV : IsAffineOpen V) (e : Γ(X, V)) (he :
    X.basicOpen e ≤ V')
    (g : Γ(X, V')) :
    ∃ (p : Γ(X, V)) (n : ℕ), ∀ {L : Type u} [Field L] (a : Spec (CommRingCat.of L) ⟶ X)
      (h : ⊤ ≤ a ⁻¹ᵁ V), evalHom a V h e ≠ 0 →
      ∃ h' : ⊤ ≤ a ⁻¹ᵁ V', evalHom a V' h' g * (evalHom a V h e) ^ n = evalHom a V h p := by
  have := hV.isLocalization_basicOpen e
  obtain ⟨⟨p, ⟨_, n, rfl⟩⟩, hp⟩ :=
    IsLocalization.surj (Submonoid.powers e) (X.presheaf.map (homOfLE he).op g)
  refine ⟨p, n, fun {L} _ a h hne => ?_⟩
  have hD : ⊤ ≤ a ⁻¹ᵁ X.basicOpen e := (top_le_preimage_basicOpen_iff a h e).mpr hne
  have h' : ⊤ ≤ a ⁻¹ᵁ V' := hD.trans (Scheme.Hom.preimage_mono a he)
  refine ⟨h', ?_⟩
  have hp' := congrArg (evalHom a (X.basicOpen e) hD) hp
  rw [map_mul, evalHom_map a h' hD he] at hp'
  change _ * evalHom a (X.basicOpen e) hD (X.presheaf.map (homOfLE (X.basicOpen_le e)).op (e ^ n)) =
    evalHom a (X.basicOpen e) hD (X.presheaf.map (homOfLE (X.basicOpen_le e)).op p) at hp'
  rwa [evalHom_map a h hD, evalHom_map a h hD, map_pow] at hp'

theorem evalHom_congr {L : Type u} [CommRing L] {a b : Spec (CommRingCat.of L) ⟶ X} (hab : a = b) (V
    : X.Opens)
    (ha : ⊤ ≤ a ⁻¹ᵁ V) (hb : ⊤ ≤ b ⁻¹ᵁ V) : evalHom a V ha = evalHom b V hb := by
  subst hab; rfl

theorem eq_specMap_evalHom_comp_fromSpec {L : Type u} [CommRing L] (a : Spec (CommRingCat.of L) ⟶ X)
    {V : X.Opens} (hV : IsAffineOpen V) (h : ⊤ ≤ a ⁻¹ᵁ V) :
    a = Spec.map (CommRingCat.ofHom (evalHom a V h)) ≫ hV.fromSpec := by
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec a hV (isAffineOpen_top (Spec (CommRingCat.of L))) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h1
  rw [ofHom_evalHom, Spec.map_comp, Category.assoc, h1, ← Spec.map_comp_assoc, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

theorem evalHom_specMap_comp_fromSpec {L : Type u} [CommRing L] {V : X.Opens} (hV : IsAffineOpen V)
    (Φ : Γ(X, V) →+* L) (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom Φ) ≫ hV.fromSpec) ⁻¹ᵁ V) :
    evalHom (Spec.map (CommRingCat.ofHom Φ) ≫ hV.fromSpec) V h = Φ := by
  have h1 := eq_specMap_evalHom_comp_fromSpec (Spec.map (CommRingCat.ofHom Φ) ≫ hV.fromSpec) hV h
  rw [cancel_mono, Spec.map_inj] at h1
  exact (congrArg CommRingCat.Hom.hom h1).symm

theorem top_le_preimage_of_mem {L : Type u} [CommRing L] [IsLocalRing L] (a : Spec (CommRingCat.of
    L) ⟶ X)
    {V : X.Opens} (h : a.base (IsLocalRing.closedPoint L) ∈ V) : ⊤ ≤ a ⁻¹ᵁ V := by
  rintro x -
  change a.base x ∈ V
  exact ((IsLocalRing.specializes_closedPoint x).map a.base.hom.continuous).mem_open V.2 h

variable {K : Type u} [Field K] (f : X ⟶ Spec (CommRingCat.of K))

/-- The base-field coefficient map on sections of the given open. -/
def algK (V : X.Opens) : K →+* Γ(X, V) :=
  (f.appLE ⊤ V (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem ofHom_algK (V : X.Opens) :
    CommRingCat.ofHom (algK f V) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ V (fun _ _ => trivial) :=
  rfl

theorem fromSpec_comp_eq {V : X.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algK f V)) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (CommRingCat.of K))) hV
    (le_top : V ≤ f ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  rw [← h, ofHom_algK]

theorem evalHom_comp_algK {L : Type u} [CommRing L] (φ : K →+* L) (a : Spec (CommRingCat.of L) ⟶ X)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom φ)) (V : X.Opens) (h : ⊤ ≤ a ⁻¹ᵁ V) :
    (evalHom a V h).comp (algK f V) = φ := by
  have h1 : f.appLE ⊤ V (fun _ _ => trivial) ≫ a.appLE V ⊤ h =
      (Spec.map (CommRingCat.ofHom φ)).appTop := by
    calc
      _ = (a ≫ f).appLE ⊤ ⊤ (fun _ _ => trivial) :=
        Scheme.Hom.appLE_comp_appLE a f ⊤ V ⊤ _ h
      _ = (a ≫ f).appTop := Scheme.Hom.appLE_eq_app _
      _ = (Spec.map (CommRingCat.ofHom φ)).appTop := congrArg Scheme.Hom.appTop ha
  have h2 : CommRingCat.ofHom ((evalHom a V h).comp (algK f V)) = CommRingCat.ofHom φ := by
    rw [CommRingCat.ofHom_comp, ofHom_evalHom, ofHom_algK, Category.assoc,
      reassoc_of% h1, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congrArg CommRingCat.Hom.hom h2

end Eval

section Ultra

variable {J : Type u} (L : J → Type u) [∀ j, Field (L j)] (𝔘 : Ultrafilter J)

/-- Functions vanishing on an ultrafilter-large set. -/
def nullIdeal : Ideal (Π j, L j) where
  carrier := {x | ∀ᶠ j in 𝔘, x j = 0}
  add_mem' {x y} hx hy := by
    filter_upwards [hx, hy] with j hxj hyj
    change x j + y j = 0
    rw [hxj, hyj, add_zero]
  zero_mem' := Filter.Eventually.of_forall (fun _ => rfl)
  smul_mem' r {x} hx := by
    filter_upwards [hx] with j hxj
    change r j * x j = 0
    rw [hxj, mul_zero]

/-- The quotient defining the ultraproduct of the given fields. -/
def UProd : Type u := (Π j, L j) ⧸ nullIdeal L 𝔘

scoped instance : CommRing (UProd L 𝔘) := inferInstanceAs (CommRing ((Π j, L j) ⧸ nullIdeal L 𝔘))

/-- The canonical quotient map to the ultraproduct. -/
def cls : (Π j, L j) →+* UProd L 𝔘 := Ideal.Quotient.mk (nullIdeal L 𝔘)

variable {L 𝔘}

theorem cls_surjective : Function.Surjective (cls L 𝔘) := Ideal.Quotient.mk_surjective

theorem cls_eq_cls_iff {x y : Π j, L j} : cls L 𝔘 x = cls L 𝔘 y ↔ ∀ᶠ j in 𝔘, x j = y j := by
  change Ideal.Quotient.mk _ x = Ideal.Quotient.mk _ y ↔ _
  rw [Ideal.Quotient.eq]
  change (∀ᶠ j in 𝔘, (x - y) j = 0) ↔ _
  simp only [Pi.sub_apply, sub_eq_zero]

theorem cls_eq_zero_iff {x : Π j, L j} : cls L 𝔘 x = 0 ↔ ∀ᶠ j in 𝔘, x j = 0 := by
  rw [← map_zero (cls L 𝔘), cls_eq_cls_iff]; rfl

theorem cls_ne_zero_iff {x : Π j, L j} : cls L 𝔘 x ≠ 0 ↔ ∀ᶠ j in 𝔘, x j ≠ 0 := by
  rw [Ne, cls_eq_zero_iff, Ultrafilter.eventually_not]

variable (L 𝔘) in
theorem isField_uProd : IsField (UProd L 𝔘) where
  exists_pair_ne := ⟨0, 1, fun h => by
    have h' : cls L 𝔘 0 = cls L 𝔘 1 := by simpa only [map_zero, map_one] using h
    rw [cls_eq_cls_iff] at h'
    obtain ⟨j, hj⟩ := h'.exists
    exact zero_ne_one hj⟩
  mul_comm := mul_comm
  mul_inv_cancel {x} hx := by
    obtain ⟨x, rfl⟩ := cls_surjective x
    refine ⟨cls L 𝔘 (fun j => (x j)⁻¹), ?_⟩
    rw [← map_mul, ← map_one (cls L 𝔘), cls_eq_cls_iff]
    filter_upwards [cls_ne_zero_iff.mp hx] with j hj
    exact mul_inv_cancel₀ hj

scoped instance : Field (UProd L 𝔘) := (isField_uProd L 𝔘).toField

theorem cls_inv (x : Π j, L j) : cls L 𝔘 (fun j => (x j)⁻¹) = (cls L 𝔘 x)⁻¹ := by
  by_cases hx : cls L 𝔘 x = 0
  · rw [hx, inv_zero, cls_eq_zero_iff]
    filter_upwards [cls_eq_zero_iff.mp hx] with j hj
    rw [hj, inv_zero]
  · symm
    apply inv_eq_of_mul_eq_one_right
    rw [← map_mul, ← map_one (cls L 𝔘), cls_eq_cls_iff]
    filter_upwards [cls_ne_zero_iff.mp hx] with j hj
    exact mul_inv_cancel₀ hj

/-- The subring of classes represented by almost-everywhere subring elements. -/
def uSubring (S : ∀ j, Subring (L j)) : Subring (UProd L 𝔘) :=
  Subring.map (cls L 𝔘)
    { carrier := {x | ∀ᶠ j in 𝔘, x j ∈ S j}
      mul_mem' {x y} hx hy := by
        filter_upwards [hx, hy] with j hxj hyj
        exact (S j).mul_mem hxj hyj
      one_mem' := Filter.Eventually.of_forall (fun j => (S j).one_mem)
      add_mem' {x y} hx hy := by
        filter_upwards [hx, hy] with j hxj hyj
        exact (S j).add_mem hxj hyj
      zero_mem' := Filter.Eventually.of_forall (fun j => (S j).zero_mem)
      neg_mem' {x} hx := by
        filter_upwards [hx] with j hxj
        exact (S j).neg_mem hxj }

theorem cls_mem_uSubring_iff {S : ∀ j, Subring (L j)} {x : Π j, L j} :
    cls L 𝔘 x ∈ uSubring S ↔ ∀ᶠ j in 𝔘, x j ∈ S j := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    filter_upwards [hy, cls_eq_cls_iff.mp hxy] with j hyj hxyj
    rwa [← hxyj]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem mem_uSubring_or_inv_mem (S : ∀ j, ValuationSubring (L j)) (x : UProd L 𝔘) :
    x ∈ uSubring (fun j => (S j).toSubring) ∨ x⁻¹ ∈ uSubring (fun j => (S j).toSubring) := by
  obtain ⟨x, rfl⟩ := cls_surjective x
  rcases 𝔘.em (fun j => x j ∈ (S j).toSubring) with h | h
  · exact Or.inl (cls_mem_uSubring_iff.mpr h)
  · right
    rw [← cls_inv, cls_mem_uSubring_iff]
    filter_upwards [h] with j hj
    exact ((S j).mem_or_inv_mem (x j)).resolve_left hj

/-- Saturate a subring by the nonzero base-ring elements. -/
def saturation {R M : Type*} [CommRing R] [IsDomain R] [Field M] (φ : R →+* M) (V : Subring M)
    (hV : ∀ x : M, x ∈ V ∨ x⁻¹ ∈ V) (hR : ∀ r, φ r ∈ V) : ValuationSubring M where
  carrier := {x | ∃ r : R, r ≠ 0 ∧ φ r * x ∈ V}
  mul_mem' := by
    rintro x y ⟨r, hr, hx⟩ ⟨t, ht, hy⟩
    refine ⟨r * t, mul_ne_zero hr ht, ?_⟩
    have : φ (r * t) * (x * y) = (φ r * x) * (φ t * y) := by rw [map_mul]; ring
    rw [this]; exact mul_mem hx hy
  one_mem' := ⟨1, one_ne_zero, by simpa only [map_one, one_mul] using hR 1⟩
  add_mem' := by
    rintro x y ⟨r, hr, hx⟩ ⟨t, ht, hy⟩
    refine ⟨r * t, mul_ne_zero hr ht, ?_⟩
    have : φ (r * t) * (x + y) = φ t * (φ r * x) + φ r * (φ t * y) := by rw [map_mul]; ring
    rw [this]; exact add_mem (mul_mem (hR t) hx) (mul_mem (hR r) hy)
  zero_mem' := ⟨1, one_ne_zero, by rw [mul_zero]; exact V.zero_mem⟩
  neg_mem' := by
    rintro x ⟨r, hr, hx⟩
    exact ⟨r, hr, by rw [mul_neg]; exact neg_mem hx⟩
  mem_or_inv_mem' x := by
    rcases hV x with h | h
    · exact Or.inl ⟨1, one_ne_zero, by simpa only [map_one, one_mul] using h⟩
    · exact Or.inr ⟨1, one_ne_zero, by simpa only [map_one, one_mul] using h⟩

end Ultra

section Main

variable {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing
    R K]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
variable {ι : Type v} (U : ι → X.Opens) (s : ∀ i, Finset Γ(X, U i))

/-- A field-valued obstruction to a uniform valuative bound. -/
structure BadDatum (c : R) where
  /-- The test field. -/
  L : Type u
  /-- The field structure. -/
  [fld : Field L]
  /-- The base-ring algebra structure. -/
  [algR : Algebra R L]
  /-- The fraction-field algebra structure. -/
  [algK : Algebra K L]
  /-- Compatibility of the two algebra structures. -/
  [tow : IsScalarTower R K L]
  /-- The test valuation subring. -/
  V : ValuationSubring L
  /-- The base ring maps into the valuation subring. -/
  hRV : ∀ r : R, algebraMap R L r ∈ V
  /-- The test point of the scheme. -/
  a : Spec (CommRingCat.of L) ⟶ X
  /-- The point lies over the chosen fraction-field map. -/
  ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L))
  /-- Some chosen section violates the proposed bound on every admissible open. -/
  bad : ∀ (i : ι) (h : ⊤ ≤ a ⁻¹ᵁ U i), ∃ g ∈ s i, algebraMap R L c * evalHom a (U i) h g ∉ V

attribute [local instance] BadDatum.fld BadDatum.algR BadDatum.algK BadDatum.tow

variable {K f U s}

theorem false_of_badDatum [IsProper f] (hcov : ⨆ i, U i = ⊤)
    (d : ∀ c : {c : R // c ≠ 0}, BadDatum K f U s c.1) : False := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒲 := X.affineCover.finiteSubcover
  let W : 𝒲.I₀ → X.Opens := fun j => (𝒲.f j).opensRange
  have hWaff : ∀ j, IsAffineOpen (W j) := fun j => isAffineOpen_opensRange (𝒲.f j)
  have hWcov : ⨆ j, W j = ⊤ := 𝒲.iSup_opensRange
  have : Nonempty {c : R // c ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  let F : Filter {c : R // c ≠ 0} := ⨅ c₀ : {c : R // c ≠ 0}, 𝓟 {c | c₀.1 ∣ c.1}
  have hF : F.NeBot := by
    refine Filter.iInf_neBot_of_directed' ?_ (fun c₀ => Filter.principal_neBot_iff.mpr ⟨c₀,
      dvd_rfl⟩)
    intro c₁ c₂
    refine ⟨⟨c₁.1 * c₂.1, mul_ne_zero c₁.2 c₂.2⟩, ?_, ?_⟩
    · exact Filter.principal_mono.mpr fun c (hc : c₁.1 * c₂.1 ∣ c.1) => (dvd_mul_right c₁.1
      c₂.1).trans hc
    · exact Filter.principal_mono.mpr fun c (hc : c₁.1 * c₂.1 ∣ c.1) => (dvd_mul_left c₂.1
      c₁.1).trans hc
  let 𝔘 : Ultrafilter {c : R // c ≠ 0} := Ultrafilter.of F
  have hdvd : ∀ c₀ : {c : R // c ≠ 0}, ∀ᶠ c in (𝔘 : Filter {c : R // c ≠ 0}), c₀.1 ∣ c.1 := fun
    c₀ =>
    Ultrafilter.of_le F (Filter.mem_iInf_of_mem c₀ (Filter.mem_principal_self _))
  let Lc : {c : R // c ≠ 0} → Type u := fun c => (d c).L
  let Lu : Type u := UProd Lc 𝔘
  let Vu : Subring Lu := uSubring (fun c => ((d c).V).toSubring)
  let φR : R →+* Lu := (cls Lc 𝔘).comp (RingHom.pi fun c => algebraMap R (d c).L)
  let φK : K →+* Lu := (cls Lc 𝔘).comp (RingHom.pi fun c => algebraMap K (d c).L)
  have hφ : φK.comp (algebraMap R K) = φR := by
    ext r
    change cls Lc 𝔘 _ = cls Lc 𝔘 _
    congr 1
    funext c
    exact (IsScalarTower.algebraMap_apply R K (d c).L r).symm
  have hRV : ∀ r, φR r ∈ Vu := fun r =>
    cls_mem_uSubring_iff.mpr (Filter.Eventually.of_forall fun c => (d c).hRV r)
  let W' : ValuationSubring Lu :=
    saturation φR Vu (mem_uSubring_or_inv_mem (fun c => (d c).V)) hRV
  have hKW : ∀ k, φK k ∈ W' := by
    intro k
    obtain ⟨n, m, hm, rfl⟩ := IsFractionRing.div_surjective (A := R) k
    change ∃ r : R, r ≠ 0 ∧ φR r * φK _ ∈ Vu
    refine ⟨m, nonZeroDivisors.ne_zero hm, ?_⟩
    have hm' : algebraMap R K m ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
    have : φR m * φK (algebraMap R K n / algebraMap R K m) = φR n := by
      rw [← hφ]
      change φK (algebraMap R K m) * φK _ = φK (algebraMap R K n)
      rw [← map_mul, mul_div_cancel₀ _ hm']
    rw [this]
    exact hRV n
  let φKW : K →+* W' := φK.codRestrict W'.toSubring hKW
  have hall : ∀ c : {c : R // c ≠ 0}, ∃ j, ⊤ ≤ (d c).a ⁻¹ᵁ W j := fun c => by
    have hx : (d c).a.base default ∈ (⊤ : X.Opens) := trivial
    rw [← hWcov, TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨j, hj⟩ := hx
    exact ⟨j, (top_le_preimage_iff _ _).mpr hj⟩
  obtain ⟨j₀, hj₀⟩ : ∃ j, ∀ᶠ c in (𝔘 : Filter {c : R // c ≠ 0}), ⊤ ≤ (d c).a ⁻¹ᵁ W j :=
    Ultrafilter.eventually_exists_iff.mp (Filter.Eventually.of_forall hall)
  let ev : Γ(X, W j₀) → Π c : {c : R // c ≠ 0}, Lc c := fun g c =>
    if h : ⊤ ≤ (d c).a ⁻¹ᵁ W j₀ then evalHom (d c).a (W j₀) h g else 0
  have hev : ∀ (g) (c : {c : R // c ≠ 0}) (h : ⊤ ≤ (d c).a ⁻¹ᵁ W j₀), ev g c = evalHom (d c).a (W
    j₀) h g :=
    fun g c h => dite_eq_left h
  let Φ : Γ(X, W j₀) →+* Lu :=
    { toFun := fun g => cls Lc 𝔘 (ev g)
      map_one' := by
        rw [← map_one (cls Lc 𝔘), cls_eq_cls_iff]
        filter_upwards [hj₀] with c hc
        rw [hev _ c hc, map_one]; rfl
      map_mul' := fun x y => by
        rw [← map_mul, cls_eq_cls_iff]
        filter_upwards [hj₀] with c hc
        rw [Pi.mul_apply, hev _ c hc, hev _ c hc, hev _ c hc, map_mul]
      map_zero' := by
        rw [← map_zero (cls Lc 𝔘), cls_eq_cls_iff]
        filter_upwards [hj₀] with c hc
        rw [hev _ c hc, map_zero]; rfl
      map_add' := fun x y => by
        rw [← map_add, cls_eq_cls_iff]
        filter_upwards [hj₀] with c hc
        rw [Pi.add_apply, hev _ c hc, hev _ c hc, hev _ c hc, map_add] }
  have hΦ_apply : ∀ g, Φ g = cls Lc 𝔘 (ev g) := fun g => rfl
  have hΦK : Φ.comp (algK f (W j₀)) = φK := by
    ext k
    change cls Lc 𝔘 _ = cls Lc 𝔘 _
    rw [cls_eq_cls_iff]
    filter_upwards [hj₀] with c hc
    rw [hev _ c hc, ← RingHom.comp_apply, evalHom_comp_algK f (algebraMap K (d c).L) (d c).a (d
      c).ha]
    rfl
  obtain ⟨a, ha_def⟩ :
      ∃ a : Spec (CommRingCat.of Lu) ⟶ X, a = Spec.map (CommRingCat.ofHom Φ) ≫ (hWaff
        j₀).fromSpec :=
    ⟨_, rfl⟩
  have ha : a ≫ f = Spec.map (CommRingCat.ofHom φK) := by
    rw [ha_def, Category.assoc, fromSpec_comp_eq f (hWaff j₀), ← Spec.map_comp, ←
      CommRingCat.ofHom_comp,
      hΦK]
  have ha₀ : ⊤ ≤ a ⁻¹ᵁ W j₀ := by
    rw [ha_def, top_le_iff]
    change Spec.map (CommRingCat.ofHom Φ) ⁻¹ᵁ ((hWaff j₀).fromSpec ⁻¹ᵁ W j₀) = ⊤
    rw [IsAffineOpen.fromSpec_preimage_self]
    rfl
  have hΦ : evalHom a (W j₀) ha₀ = Φ := by
    subst ha_def
    exact evalHom_specMap_comp_fromSpec (hWaff j₀) Φ ha₀
  have hVC : ValuativeCriterion.Existence f := by
    have hp : IsProper f := inferInstance
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1.existence
  have sq : CommSq a (Spec.map (CommRingCat.ofHom (algebraMap W' Lu))) f (Spec.map
    (CommRingCat.ofHom φKW)) := by
    constructor
    rw [ha, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let S : ValuativeCommSq f :=
    { R := W', K := Lu, i₁ := a, i₂ := Spec.map (CommRingCat.ofHom φKW), commSq := sq }
  obtain ⟨⟨l, hl₁, _hl₂⟩⟩ := (hVC S).exists_lift
  change Spec.map (CommRingCat.ofHom (algebraMap W' Lu)) ≫ l = a at hl₁
  obtain ⟨i₁, hi₁⟩ : ∃ i, l.base (IsLocalRing.closedPoint W') ∈ U i := by
    have hx : l.base (IsLocalRing.closedPoint W') ∈ (⊤ : X.Opens) := trivial
    rwa [← hcov, TopologicalSpace.Opens.mem_iSup] at hx
  have hl₁' : ⊤ ≤ l ⁻¹ᵁ U i₁ := top_le_preimage_of_mem l hi₁
  have ha₁ : ⊤ ≤ a ⁻¹ᵁ U i₁ := by
    rw [← hl₁]; exact fun x _ => hl₁' (Set.mem_univ _)
  have hW : ∀ g : Γ(X, U i₁), ∃ r : R, r ≠ 0 ∧ φR r * evalHom a (U i₁) ha₁ g ∈ Vu := by
    intro g
    have hmem : evalHom a (U i₁) ha₁ g ∈ W' := by
      rw [evalHom_congr hl₁.symm (U i₁) ha₁ (by rw [hl₁]; exact ha₁),
        evalHom_specMap_comp (algebraMap W' Lu) l (U i₁) hl₁']
      exact (evalHom l (U i₁) hl₁' g).2
    exact hmem
  obtain ⟨e, he, hxe⟩ := (hWaff j₀).exists_basicOpen_le
    ⟨a.base default, (top_le_preimage_iff a _).mp ha₁⟩ ((top_le_preimage_iff a _).mp ha₀)
  have hea : evalHom a (W j₀) ha₀ e ≠ 0 :=
    (top_le_preimage_basicOpen_iff a ha₀ e).mp ((top_le_preimage_iff a _).mpr hxe)
  have he𝔘 : ∀ᶠ c in (𝔘 : Filter {c : R // c ≠ 0}),
      ∃ h : ⊤ ≤ (d c).a ⁻¹ᵁ W j₀, evalHom (d c).a (W j₀) h e ≠ 0 := by
    have hne : Φ e ≠ 0 := by rwa [← hΦ]
    rw [hΦ_apply, cls_ne_zero_iff] at hne
    filter_upwards [hne, hj₀] with c hc hc₀
    exact ⟨hc₀, by rwa [← hev e c hc₀]⟩
  have key : ∀ g : Γ(X, U i₁), ∃ r : R, r ≠ 0 ∧ ∀ᶠ c in (𝔘 : Filter {c : R // c ≠ 0}),
      ∃ h : ⊤ ≤ (d c).a ⁻¹ᵁ U i₁, algebraMap R (d c).L r * evalHom (d c).a (U i₁) h g ∈ (d
        c).V := by
    intro g
    obtain ⟨r, hr, hrg⟩ := hW g
    obtain ⟨p, n, hp⟩ := exists_eval_mul_pow_eq (hWaff j₀) e he g
    obtain ⟨h₁', hpa⟩ := hp a ha₀ hea
    obtain ⟨q, hq⟩ := cls_surjective (evalHom a (U i₁) ha₁ g)
    refine ⟨r, hr, ?_⟩
    have h1 : ∀ᶠ c in (𝔘 : Filter {c : R // c ≠ 0}), algebraMap R (d c).L r * q c ∈ (d c).V := by
      have : φR r * evalHom a (U i₁) ha₁ g = cls Lc 𝔘 (fun c => algebraMap R (d c).L r * q c) := by
        rw [← hq]; rfl
      rw [this] at hrg
      exact cls_mem_uSubring_iff.mp hrg
    have h2 : ∀ᶠ c in (𝔘 : Filter {c : R // c ≠ 0}), q c * (ev e c) ^ n = ev p c := by
      have : cls Lc 𝔘 (fun c => q c * (ev e c) ^ n) = cls Lc 𝔘 (ev p) := by
        rw [← hΦ_apply p, ← hΦ, ← hpa, show evalHom a (U i₁) h₁' g = evalHom a (U i₁) ha₁ g from
          rfl, ← hq,
          hΦ, hΦ_apply, ← map_pow, ← map_mul]
        rfl
      exact cls_eq_cls_iff.mp this
    filter_upwards [h1, h2, he𝔘] with c hc1 hc2 hce
    obtain ⟨hc₀, hce⟩ := hce
    obtain ⟨hc₁, hcomp⟩ := hp (d c).a hc₀ hce
    refine ⟨hc₁, ?_⟩
    rw [hev e c hc₀, hev p c hc₀, ← hcomp] at hc2
    rwa [mul_right_cancel₀ (pow_ne_zero n hce) hc2] at hc1
  choose r hr hkey using key
  have hfin : ∀ᶠ c in (𝔘 : Filter {c : R // c ≠ 0}), ∀ g ∈ s i₁, r g ∣ c.1 ∧
      ∃ h : ⊤ ≤ (d c).a ⁻¹ᵁ U i₁, algebraMap R (d c).L (r g) * evalHom (d c).a (U i₁) h g ∈ (d
        c).V :=
    (Filter.eventually_all_finset (s i₁)).mpr fun g _ => (hdvd ⟨r g, hr g⟩).and (hkey g)
  obtain ⟨c, hcfin, hc₀, hce⟩ := (hfin.and he𝔘).exists
  have hc₁ : ⊤ ≤ (d c).a ⁻¹ᵁ U i₁ :=
    ((top_le_preimage_basicOpen_iff (d c).a hc₀ e).mpr hce).trans (Scheme.Hom.preimage_mono (d c).a
      he)
  obtain ⟨g, hgs, hbad⟩ := (d c).bad i₁ hc₁
  obtain ⟨⟨t, ht⟩, ⟨h', hmem⟩⟩ := hcfin g hgs
  apply hbad
  have : algebraMap R (d c).L c.1 * evalHom (d c).a (U i₁) hc₁ g =
      algebraMap R (d c).L t * (algebraMap R (d c).L (r g) * evalHom (d c).a (U i₁) h' g) := by
    have h1 : algebraMap R (d c).L c.1 = algebraMap R (d c).L (r g) * algebraMap R (d c).L t := by
      rw [← map_mul]; exact congrArg _ ht
    rw [h1]; ring
  rw [this]
  exact mul_mem ((d c).hRV t) hmem

/-- The valuation subring in the given field of fractions. -/
def valuationSubringOf (V L : Type u) [CommRing V] [IsDomain V] [ValuationRing V] [Field L] [Algebra
    V L]
    [IsFractionRing V L] : ValuationSubring L :=
  { (algebraMap V L).range with
    mem_or_inv_mem' := fun x => by
      rcases ValuationRing.isInteger_or_isInteger V x with h | h
      · exact Or.inl h
      · exact Or.inr h }

theorem mem_valuationSubringOf_iff {V L : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Field
    L]
    [Algebra V L] [IsFractionRing V L] (x : L) :
    x ∈ valuationSubringOf V L ↔ x ∈ Set.range (algebraMap V L) :=
  Iff.rfl

end Main

end AlgebraicGeometry.ProperBounded

open AlgebraicGeometry.ProperBounded in
theorem
    _root_.AlgebraicGeometry.exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    {ι : Type v} (U : ι → X.Opens) (hcov : ⨆ i, U i = ⊤) (s : ∀ i, Finset Γ(X, U i)) :
    ∃ c : R, c ≠ 0 ∧
      ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra R V]
        (L : Type u) [Field L] [Algebra V L] [IsFractionRing V L] [Algebra R L] [IsScalarTower R V
          L]
        [Algebra K L] [IsScalarTower R K L]
        (a : Spec (CommRingCat.of L) ⟶ X), a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)) →
        ∃ (i : ι) (h : ⊤ ≤ a ⁻¹ᵁ U i), ∀ g ∈ s i,
          algebraMap R L c * (Scheme.ΓSpecIso (CommRingCat.of L)).hom (a.appLE (U i) ⊤ h g) ∈
            Set.range (algebraMap V L) := by
  by_contra H
  have hbad : ∀ c : {c : R // c ≠ 0}, Nonempty (BadDatum K f U s c.1) := by
    intro c
    by_contra hne
    apply H
    refine ⟨c.1, c.2, ?_⟩
    intro V _ _ _ _ L _ _ _ _ _ _ _ a ha
    by_contra hP
    push Not at hP
    apply hne
    exact ⟨{ L := L
             V := valuationSubringOf V L
             hRV := fun r => ⟨algebraMap R V r, (IsScalarTower.algebraMap_apply R V L r).symm⟩
             a := a
             ha := ha
             bad := fun i h => hP i h }⟩
  exact false_of_badDatum hcov fun c => (hbad c).some

end

end SchemeTheory.Properness.ValuativeBounds
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isClopen_preimage_eq_of_isProper_of_isAdicComplete.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.Properness.CompleteBaseComponents

universe u v

namespace SolPiAlg

section Lift

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)

lemma mem_pow_smul_top_iff (n : ℕ) (x : B) :
    x ∈ (I ^ n • ⊤ : Submodule A B) ↔ x ∈ (I.map (algebraMap A B)) ^ n := by
  rw [Ideal.smul_top_eq_map, Ideal.map_pow]
  rfl

lemma smodEq_iff (n : ℕ) (x y : B) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule A B)] ↔ x - y ∈ (I.map (algebraMap A B)) ^ n := by
  rw [SModEq.sub_mem, mem_pow_smul_top_iff]

/-- The cubic Newton step for lifting an idempotent. -/
def newton (x : B) : B := 3 * x ^ 2 - 2 * x ^ 3

lemma newton_sq_sub (x : B) :
    newton x ^ 2 - newton x = (x ^ 2 - x) ^ 2 * (4 * x ^ 2 - 4 * x - 3) := by
  unfold newton; ring

lemma newton_sub (x : B) : newton x - x = (x ^ 2 - x) * (1 - 2 * x) := by
  unfold newton; ring

/-- Iterate the idempotent-lifting Newton step. -/
def nseq (x₀ : B) (n : ℕ) : B := newton^[n] x₀

lemma nseq_zero (x₀ : B) : nseq x₀ 0 = x₀ := rfl

lemma nseq_succ (x₀ : B) (n : ℕ) : nseq x₀ (n + 1) = newton (nseq x₀ n) := by
  simp only [nseq, Function.iterate_succ_apply']

variable {I}

lemma nseq_sq_sub_mem (x₀ : B) (h : x₀ ^ 2 - x₀ ∈ I.map (algebraMap A B)) (n : ℕ) :
    nseq x₀ n ^ 2 - nseq x₀ n ∈ (I.map (algebraMap A B)) ^ (n + 1) := by
  induction n with
  | zero => simpa only [nseq_zero, Nat.zero_add, pow_one] using h
  | succ n ih =>
    rw [nseq_succ, newton_sq_sub]
    have : (nseq x₀ n ^ 2 - nseq x₀ n) ^ 2 ∈ (I.map (algebraMap A B)) ^ (n + 1 + 1) := by
      rw [pow_two, pow_succ _ (n + 1)]
      exact Ideal.mul_mem_mul ih (Ideal.pow_le_self (Nat.succ_ne_zero n) ih)
    exact Ideal.mul_mem_right _ _ this

lemma nseq_succ_sub_mem (x₀ : B) (h : x₀ ^ 2 - x₀ ∈ I.map (algebraMap A B)) (n : ℕ) :
    nseq x₀ (n + 1) - nseq x₀ n ∈ (I.map (algebraMap A B)) ^ (n + 1) := by
  rw [nseq_succ, newton_sub]
  exact Ideal.mul_mem_right _ _ (nseq_sq_sub_mem x₀ h n)

lemma nseq_sub_mem (x₀ : B) (h : x₀ ^ 2 - x₀ ∈ I.map (algebraMap A B)) {m n : ℕ} (hmn : m ≤ n) :
    nseq x₀ n - nseq x₀ m ∈ (I.map (algebraMap A B)) ^ m := by
  induction n, hmn using Nat.le_induction with
  | base => rw [sub_self]; exact Ideal.zero_mem _
  | succ n hmn ih =>
    have h1 := nseq_succ_sub_mem x₀ h n
    have h2 : nseq x₀ (n + 1) - nseq x₀ m
        = (nseq x₀ (n + 1) - nseq x₀ n) + (nseq x₀ n - nseq x₀ m) := by ring
    rw [h2]
    exact Ideal.add_mem _ (Ideal.pow_le_pow_right (by omega) h1) ih

variable (I)

theorem exists_isIdempotentElem_lift [IsAdicComplete I B] (x₀ : B)
    (h : x₀ ^ 2 - x₀ ∈ I.map (algebraMap A B)) :
    ∃ e : B, IsIdempotentElem e ∧ e - x₀ ∈ I.map (algebraMap A B) := by
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → nseq x₀ m ≡ nseq x₀ n [SMOD (I ^ m • ⊤ : Submodule A B)] := by
    intro m n hmn
    rw [smodEq_iff, ← neg_sub]
    exact Submodule.neg_mem _ (nseq_sub_mem x₀ h hmn)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (nseq x₀) hcauchy
  refine ⟨L, ?_, ?_⟩
  · have hzero : L ^ 2 - L = 0 := by
      refine IsHausdorff.haus' (I := I) (L ^ 2 - L) fun n => ?_
      rw [SModEq.zero, mem_pow_smul_top_iff]
      have h1 : nseq x₀ n - L ∈ (I.map (algebraMap A B)) ^ n := (smodEq_iff I n _ _).mp (hL n)
      have h2 := Ideal.pow_le_pow_right (Nat.le_succ n) (nseq_sq_sub_mem x₀ h n)
      have h3 : L ^ 2 - L = (nseq x₀ n ^ 2 - nseq x₀ n)
          - (nseq x₀ n - L) * (nseq x₀ n + L - 1) := by ring
      rw [h3]
      exact Ideal.sub_mem _ h2 (Ideal.mul_mem_right _ _ h1)
    change L * L = L
    rw [← sub_eq_zero, ← pow_two]; exact hzero
  · have h1 : nseq x₀ 1 - L ∈ (I.map (algebraMap A B)) ^ 1 := (smodEq_iff I 1 _ _).mp (hL 1)
    have h2 : nseq x₀ 1 - nseq x₀ 0 ∈ (I.map (algebraMap A B)) ^ 1 := nseq_succ_sub_mem x₀ h 0
    rw [pow_one] at h1 h2
    rw [nseq_zero] at h2
    have : L - x₀ = (nseq x₀ 1 - x₀) - (nseq x₀ 1 - L) := by ring
    rw [this]
    exact Ideal.sub_mem _ h2 h1

end Lift

section HenselLocal

open IsLocalRing

lemma isArtinianRing_quotient (A : Type u) [CommRing A] [IsLocalRing A]
    (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] :
    IsArtinianRing (B ⧸ (maximalIdeal A).map (algebraMap A B)) := by
  let : Algebra (A ⧸ maximalIdeal A) (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : IsScalarTower A (A ⧸ maximalIdeal A) (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    IsScalarTower.of_algebraMap_eq (fun a => rfl)
  have : Module.Finite A (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A _).toLinearMap Ideal.Quotient.mk_surjective
  have : Module.Finite (A ⧸ maximalIdeal A) (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    Module.Finite.of_restrictScalars_finite A _ _
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  exact IsArtinianRing.of_finite (A ⧸ maximalIdeal A) _

lemma map_maximalIdeal_le_of_isMaximal (A : Type u) [CommRing A] [IsLocalRing A]
    {B : Type u} [CommRing B] [Algebra A B] [Module.Finite A B] (M : Ideal B) [hM : M.IsMaximal] :
    (maximalIdeal A).map (algebraMap A B) ≤ M := by
  rw [Ideal.map_le_iff_le_comap]
  have hmax : (M.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap A B)
      (algebraMap_isIntegral_iff.mpr inferInstance) M
  exact (IsLocalRing.eq_maximalIdeal hmax).ge

theorem isLocalRing_of_forall_isIdempotentElem (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] [Nontrivial B]
    (h : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing B := by
  classical
  have : IsArtinianRing (B ⧸ ((maximalIdeal A).map (algebraMap A B))) :=
    isArtinianRing_quotient A B
  have : IsAdicComplete (maximalIdeal A) B :=
    IsAdicComplete.of_finite_of_isNoetherianRing (maximalIdeal A) B
  have huniq : ∀ M₁ M₂ : Ideal B, M₁.IsMaximal → M₂.IsMaximal → M₁ = M₂ := by
    intro M₁ M₂ h₁ h₂
    by_contra hne
    have hJ₁ : ((maximalIdeal A).map (algebraMap A B)) ≤ M₁ := map_maximalIdeal_le_of_isMaximal A M₁
    have hJ₂ : ((maximalIdeal A).map (algebraMap A B)) ≤ M₂ := map_maximalIdeal_le_of_isMaximal A M₂
    have hk : RingHom.ker (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B))) =
        (maximalIdeal A).map (algebraMap A B) := Ideal.mk_ker
    have hp₁ : (M₁.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)))).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (hk.symm ▸ hJ₁)
    have hp₂ : (M₂.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)))).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (hk.symm ▸ hJ₂)
    have hc₁ : (M₁.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)))).comap
        (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B))) = M₁ := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        hk, sup_eq_left.mpr hJ₁]
    have hc₂ : (M₂.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)))).comap
        (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B))) = M₂ := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        hk, sup_eq_left.mpr hJ₂]
    have hp : M₂.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B))) ≠
        M₁.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B))) :=
      fun heq => hne (by rw [← hc₁, ← hc₂, heq])
    have : (M₁.map (Ideal.Quotient.mk
        ((maximalIdeal A).map (algebraMap A B)))).IsPrime := hp₁.isPrime
    obtain ⟨r, hr₁, hr, hr'⟩ := IsArtinianRing.exists_notMem_forall_mem_of_ne
      (M₁.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B))))
    have hr₂ : r ∈ M₂.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B))) :=
      hr' _ hp₂.isPrime hp
    obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective r
    have hx₀ : x₀ ^ 2 - x₀ ∈ ((maximalIdeal A).map (algebraMap A B)) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero, pow_two]
      exact hr
    obtain ⟨e, he, hex⟩ := exists_isIdempotentElem_lift (maximalIdeal A) x₀ hx₀
    have hemk : Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)) e =
        Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)) x₀ := by
      rwa [Ideal.Quotient.eq]
    rcases h e he with rfl | rfl
    · rw [map_zero] at hemk
      exact hr₁ (hemk ▸ Ideal.zero_mem _)
    · rw [map_one] at hemk
      exact hp₂.ne_top ((Ideal.eq_top_iff_one _).mpr (hemk ▸ hr₂))
  obtain ⟨M, hM⟩ := Ideal.exists_maximal B
  exact IsLocalRing.of_unique_max_ideal ⟨M, hM, fun M' hM' => huniq M' M hM' hM⟩

theorem comap_eq_maximalIdeal_iff (A : Type u) [CommRing A] [IsLocalRing A]
    {B : Type u} [CommRing B] [Algebra A B] [Module.Finite A B] [IsLocalRing B]
    (p : Ideal B) [p.IsPrime] :
    p.comap (algebraMap A B) = maximalIdeal A ↔ p = maximalIdeal B := by
  constructor
  · intro hp
    have : (p.comap (algebraMap A B)).IsMaximal := hp ▸ inferInstance
    have : p.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap A B)
      (algebraMap_isIntegral_iff.mpr inferInstance) p this
    exact IsLocalRing.eq_maximalIdeal this
  · rintro rfl
    have : ((maximalIdeal B).comap (algebraMap A B)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap A B)
        (algebraMap_isIntegral_iff.mpr inferInstance) (maximalIdeal B)
    exact IsLocalRing.eq_maximalIdeal this

end HenselLocal

end SolPiAlg

namespace SolPiGeo

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Topology TopologicalSpace

section Idem

lemma isUnit_iff_not_isUnit_one_sub_of_isIdempotentElem {R : Type*} [CommRing R] [IsLocalRing R]
    {a : R} (ha : IsIdempotentElem a) : IsUnit a ↔ ¬ IsUnit (1 - a) := by
  constructor
  · intro hu hu'
    have h1 : a = 1 := by
      obtain ⟨u, rfl⟩ := hu
      have := ha.eq
      calc (u : R) = ↑u * ↑u * ↑u⁻¹ := by rw [Units.mul_inv_cancel_right]
        _ = ↑u * ↑u⁻¹ := by rw [this]
        _ = 1 := Units.mul_inv _
    rw [h1, sub_self] at hu'
    exact not_isUnit_zero hu'
  · intro h
    exact (IsLocalRing.isUnit_or_isUnit_one_sub_self a).resolve_right h

theorem isIdempotentElem_eq_zero_or_one {Q : Scheme.{u}} [CompactSpace Q] [PreconnectedSpace Q]
    (e : Γ(Q, ⊤)) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hcompl : ((Q.basicOpen e : Set Q))ᶜ = (Q.basicOpen (1 - e) : Set Q) := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe, Scheme.mem_basicOpen_top, map_sub, map_one]
    have hex : IsIdempotentElem (Q.presheaf.germ ⊤ x trivial e) := he.map _
    rw [isUnit_iff_not_isUnit_one_sub_of_isIdempotentElem hex, not_not]
  have hclopen : IsClopen (Q.basicOpen e : Set Q) := by
    refine ⟨?_, (Q.basicOpen e).isOpen⟩
    rw [← isOpen_compl_iff, hcompl]
    exact (Q.basicOpen (1 - e)).isOpen
  rcases isClopen_iff.mp hclopen with h | h
  · left
    have hbot : Q.basicOpen e = ⊥ := by
      exact TopologicalSpace.Opens.ext h
    obtain ⟨n, hn⟩ := (Scheme.isNilpotent_iff_basicOpen_eq_bot e).mpr hbot
    calc e = e ^ (n + 1) := (he.pow_succ_eq n).symm
      _ = 0 := by rw [pow_succ, hn, zero_mul]
  · right
    have hbot : Q.basicOpen (1 - e) = ⊥ := by
      apply TopologicalSpace.Opens.ext
      simp only [TopologicalSpace.Opens.coe_bot]
      rw [← hcompl, h, Set.compl_univ]
    obtain ⟨n, hn⟩ := (Scheme.isNilpotent_iff_basicOpen_eq_bot (1 - e)).mpr hbot
    have h1 : (1 - e) = 0 := by
      calc (1 - e) = (1 - e) ^ (n + 1) := (he.one_sub.pow_succ_eq n).symm
        _ = 0 := by rw [pow_succ, hn, zero_mul]
    exact (sub_eq_zero.mp h1).symm

end Idem

section Conn

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  [IsAdicComplete (maximalIdeal A) A]

omit [IsNoetherianRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] in
lemma apply_eq_comap_toSpecΓ {Q : Scheme.{u}} (g : Q ⟶ Spec (CommRingCat.of A)) (y : Q) :
    g y = PrimeSpectrum.comap (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (Q.toSpecΓ y) := by
  have hnat := Scheme.toSpecΓ_naturality g
  rw [← SpecMap_ΓSpecIso_hom] at hnat
  have h1 : (Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom) (g y)
      = (Spec.map g.appTop) (Q.toSpecΓ y) := by
    have := congrArg (fun h : Q ⟶ _ => h y) hnat
    simpa only [Scheme.Hom.comp_apply] using this
  rw [Spec.map_apply, Spec.map_apply] at h1
  have h2 := congrArg (PrimeSpectrum.comap (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) h1
  change PrimeSpectrum.comap
      ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) (g y) =
    PrimeSpectrum.comap
      (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) (Q.toSpecΓ y) at h2
  have h3 : ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) = RingHom.id A := by
    rw [← CommRingCat.hom_comp, CategoryTheory.Iso.inv_hom_id, CommRingCat.hom_id]
  rw [h3, PrimeSpectrum.comap_id] at h2
  exact h2

theorem isPreconnected_fibre_of_connectedSpace {Q : Scheme.{u}} (g : Q ⟶ Spec (CommRingCat.of A))
    [IsProper g] [ConnectedSpace Q] : _root_.IsPreconnected (g ⁻¹' {closedPoint A}) := by
  have : CompactSpace Q := QuasiCompact.compactSpace_of_compactSpace g
  let φ : A →+* Γ(Q, ⊤) := g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  let : Algebra A Γ(Q, ⊤) := φ.toAlgebra
  have : Module.Finite A Γ(Q, ⊤) := by
    have hF : g.appTop.hom.Finite :=
      AlgebraicGeometry.finite_appTop_of_isProper_of_isNoetherianRing g
    have : φ.Finite := RingHom.Finite.comp hF (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.surjective)
    exact this
  have : Nonempty (⊤ : Q.Opens) := ⟨⟨Classical.arbitrary Q, trivial⟩⟩
  have : Nontrivial Γ(Q, ⊤) := inferInstance
  have : IsLocalRing Γ(Q, ⊤) := SolPiAlg.isLocalRing_of_forall_isIdempotentElem A Γ(Q, ⊤)
    (fun e he => isIdempotentElem_eq_zero_or_one e he)
  have : IsNoetherianRing Γ(Q, ⊤) := IsNoetherianRing.of_finite A Γ(Q, ⊤)
  have : IsProper (Q.toSpecΓ ≫ Spec.map g.appTop) := by
    rw [← Scheme.toSpecΓ_naturality]; infer_instance
  have : IsProper Q.toSpecΓ := IsProper.of_comp _ (Spec.map g.appTop)
  have hbij : Function.Bijective Q.toSpecΓ.appTop := by
    rw [Scheme.toSpecΓ_appTop]; exact ConcreteCategory.bijective_of_isIso _
  have key : _root_.IsPreconnected (Q.toSpecΓ ⁻¹' {closedPoint Γ(Q, ⊤)}) :=
    AlgebraicGeometry.isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop
      (A := Γ(Q, ⊤)) Q.toSpecΓ hbij
  suffices hfib : g ⁻¹' {closedPoint A} = Q.toSpecΓ ⁻¹' {closedPoint Γ(Q, ⊤)} by
    rwa [hfib]
  ext y
  simp only [Set.mem_preimage]
  rw [apply_eq_comap_toSpecΓ g y]
  have : (Q.toSpecΓ y).asIdeal.IsPrime := (Q.toSpecΓ y).isPrime
  constructor
  · intro h
    have h' : (Q.toSpecΓ y).asIdeal.comap (algebraMap A Γ(Q, ⊤)) = maximalIdeal A :=
      congrArg PrimeSpectrum.asIdeal h
    exact PrimeSpectrum.ext ((SolPiAlg.comap_eq_maximalIdeal_iff A _).mp h')
  · intro h
    rw [h]
    exact PrimeSpectrum.ext ((SolPiAlg.comap_eq_maximalIdeal_iff A _).mpr rfl)

end Conn

section Components

theorem isOpen_connectedComponent' {X : Type*} [TopologicalSpace X] [NoetherianSpace X] (x : X) :
    IsOpen (connectedComponent x) := by
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  have hcompl : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents X | Disjoint Z (connectedComponent x)}, Z := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hy
      refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩,
        mem_irreducibleComponent⟩
      rw [Set.disjoint_left]
      intro z hz hzx
      have h1 : irreducibleComponent y ⊆ connectedComponent z :=
        isIrreducible_irreducibleComponent.isConnected.subset_connectedComponent hz
      have h2 : connectedComponent x = connectedComponent z := connectedComponent_eq hzx
      exact hy (h2 ▸ h1 mem_irreducibleComponent)
    · rintro ⟨Z, ⟨-, hdisj⟩, hyZ⟩ hy
      exact Set.disjoint_left.mp hdisj hyZ hy
  rw [← isClosed_compl_iff, hcompl]
  exact (hfin.subset (Set.sep_subset _ _)).isClosed_biUnion
    fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1

end Components

section ClosedPointOfField

variable {R : Type u} [CommRing R] [IsLocalRing R] {K : Type u} [Field K]
  (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion ι]

omit [IsLocalRing R] in
lemma surjective_preimage : Function.Surjective (Spec.preimage ι).hom := by
  have h : Function.Surjective (ι.appTop) := ι.app_surjective ⊤ (isAffineOpen_top _)
  have hnat := Scheme.ΓSpecIso_naturality (Spec.preimage ι)
  rw [Spec.map_preimage] at hnat
  have heq : (Spec.preimage ι) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ ι.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
    rw [hnat, CategoryTheory.Iso.inv_hom_id_assoc]
  have hsurj : Function.Surjective
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ ι.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom := by
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    exact ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.surjective.comp h).comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.surjective
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨x, by rw [heq]; exact hx⟩

lemma apply_eq_closedPoint (z : Spec (CommRingCat.of K)) : ι z = closedPoint R := by
  have hι : ι = Spec.map (Spec.preimage ι) := (Spec.map_preimage ι).symm
  rw [hι]
  apply PrimeSpectrum.ext
  change Ideal.comap (Spec.preimage ι).hom z.asIdeal = maximalIdeal R
  have hz : z.asIdeal = ⊥ := (Ideal.eq_bot_or_top z.asIdeal).resolve_right z.isPrime.ne_top
  rw [hz, ← RingHom.ker_eq_comap_bot]
  exact IsLocalRing.eq_maximalIdeal
    (RingHom.ker_isMaximal_of_surjective _ (surjective_preimage ι))

lemma range_eq : Set.range ι = {closedPoint R} := by
  ext p
  simp only [Set.mem_range]
  exact ⟨fun ⟨z, hz⟩ => hz ▸ apply_eq_closedPoint ι z, fun h => ⟨closedPoint K, h ▸
    apply_eq_closedPoint ι _⟩⟩

end ClosedPointOfField

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  [IsAdicComplete (maximalIdeal A) A]
  {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
  {K : Type u} [Field K] (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A))
  [IsClosedImmersion ι]

lemma isPreconnected_preimage_connectedComponent (x : P) :
    _root_.IsPreconnected (pullback.fst q ι ⁻¹' connectedComponent x) := by
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian P := {}
  let U : P.Opens := ⟨connectedComponent x, isOpen_connectedComponent' x⟩
  have : ConnectedSpace U := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have : ConnectedSpace (U : Scheme.{u}) := ‹ConnectedSpace U›
  have : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _
    (by rw [Scheme.Opens.range_ι]; exact isClosed_connectedComponent)
  have h1 : _root_.IsPreconnected ((U.ι ≫ q) ⁻¹' {closedPoint A}) :=
    isPreconnected_fibre_of_connectedSpace (U.ι ≫ q)
  have h2 : _root_.IsPreconnected (U.ι '' ((U.ι ≫ q) ⁻¹' {closedPoint A})) :=
    h1.image _ U.ι.continuous.continuousOn
  have h3 : U.ι '' ((U.ι ≫ q) ⁻¹' {closedPoint A}) =
      connectedComponent x ∩ q ⁻¹' {closedPoint A} := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage, Scheme.Hom.comp_apply,
      Set.mem_inter_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, hz⟩
    · rintro ⟨hy, hqy⟩
      exact ⟨⟨y, hy⟩, hqy, rfl⟩
  rw [h3] at h2
  have hrange : Set.range (pullback.fst q ι) = q ⁻¹' {closedPoint A} := by
    rw [Scheme.Pullback.range_fst, range_eq ι]
  have h4 : pullback.fst q ι ⁻¹' connectedComponent x
      = pullback.fst q ι ⁻¹' (connectedComponent x ∩ q ⁻¹' {closedPoint A}) := by
    ext w
    simp only [Set.mem_preimage, Set.mem_inter_iff, iff_self_and]
    intro _
    have : pullback.fst q ι w ∈ Set.range (pullback.fst q ι) := ⟨w, rfl⟩
    rw [hrange] at this
    exact this
  rw [h4]
  refine ((pullback.fst q ι).isEmbedding.isInducing.isPreconnected_image).mp ?_
  rwa [Set.image_preimage_eq_of_subset]
  rw [hrange]
  exact Set.inter_subset_right

theorem main (V₀ : Set ↥(pullback q ι)) (hV₀ : IsClopen V₀) :
    ∃ V : Set P, IsClopen V ∧ pullback.fst q ι ⁻¹' V = V₀ := by
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian P := {}
  let f := pullback.fst q ι
  refine ⟨⋃ z ∈ V₀, connectedComponent (f z), ⟨?_, ?_⟩, ?_⟩
  · rw [← isOpen_compl_iff]
    have : (⋃ z ∈ V₀, connectedComponent (f z))ᶜ =
        ⋃ y ∈ (⋃ z ∈ V₀, connectedComponent (f z))ᶜ, connectedComponent y := by
      apply subset_antisymm
      · intro y hy
        exact Set.mem_biUnion hy mem_connectedComponent
      · intro w hw
        simp only [Set.mem_iUnion, Set.mem_compl_iff, exists_prop, not_exists, not_and] at hw ⊢
        obtain ⟨y, hy, hwy⟩ := hw
        intro z hz hwz
        have e1 : connectedComponent (f z) = connectedComponent w := connectedComponent_eq hwz
        have e2 : connectedComponent y = connectedComponent w := connectedComponent_eq hwy
        exact hy z hz (by rw [e1, ← e2]; exact mem_connectedComponent)
    rw [this]
    exact isOpen_biUnion fun y _ => isOpen_connectedComponent' y
  · exact isOpen_biUnion fun z _ => isOpen_connectedComponent' (f z)
  · apply subset_antisymm
    · intro w hw
      simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop] at hw
      obtain ⟨z, hz, hwz⟩ := hw
      have hpc := isPreconnected_preimage_connectedComponent q ι (f z)
      have hsub : f ⁻¹' connectedComponent (f z) ⊆ V₀ :=
        hpc.subset_isClopen hV₀ ⟨z, mem_connectedComponent, hz⟩
      exact hsub hwz
    · intro z hz
      simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop]
      exact ⟨z, hz, mem_connectedComponent⟩

end Main

end SolPiGeo

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.exists_isClopen_preimage_eq_of_isProper_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {K : Type u} [Field K] (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A))
    [IsClosedImmersion ι]
    (V₀ : Set ↥(pullback q ι)) (hV₀ : IsClopen V₀) :
    ∃ V : Set P, IsClopen V ∧ pullback.fst q ι ⁻¹' V = V₀ :=
  SolPiGeo.main q ι V₀ hV₀

end SchemeTheory.Properness.CompleteBaseComponents
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_opens_isClosed_isProper_of_isProper_pullback_snd_of_isAdicComplete.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.Properness.ProperClopenNeighborhoods

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace ProperClopenNbhd

section ClosedPointOfField

variable {R : Type u} [CommRing R] [IsLocalRing R] {K : Type u} [Field K]
  (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion ι]

open SchemeTheory.Properness.CompleteBaseComponents.SolPiGeo (apply_eq_closedPoint)

lemma closedPoint_mem_range : closedPoint R ∈ Set.range ι :=
  ⟨closedPoint K, apply_eq_closedPoint ι _⟩

lemma exists_mem_of_isClosed {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of R))
    [UniversallyClosed q] {C : Set P} (hC : IsClosed C) {w : P} (hw : w ∈ C) :
    ∃ w' ∈ C, q w' ∈ Set.range ι := by
  have hcl : IsClosed (q '' closure {w}) := q.isClosedMap _ isClosed_closure
  have hmem : closedPoint R ∈ q '' closure {w} := by
    have hspec : q w ⤳ closedPoint R := IsLocalRing.specializes_closedPoint (q w)
    exact hspec.mem_closed hcl ⟨w, subset_closure rfl, rfl⟩
  obtain ⟨w', hw', hqw'⟩ := hmem
  exact ⟨w', (hC.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hw)) hw',
    hqw' ▸ closedPoint_mem_range ι⟩

end ClosedPointOfField

section Main

variable {A : Type u} [CommRing A] [IsLocalRing A]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  {K : Type u} [Field K] (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A))
  [IsClosedImmersion ι]
  {X' P : Scheme.{u}} (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A))
  [IsProper π] [Surjective π] [IsOpenImmersion j] [IsProper q] (hcomm : j ≫ q = π ≫ f)

/-- The projection from the closed fiber of the proper ambient scheme. -/
noncomputable abbrev pP := pullback.fst q ι

/-- The base change of the open immersion to the closed fiber. -/
noncomputable abbrev j₀ := pullback.snd j (pP ι q)

omit [IsLocalRing A] [IsClosedImmersion ι] [Surjective π]
  [IsOpenImmersion j] [IsProper q] in
include hcomm in
lemma isProper_j₀_comp [IsProper (pullback.snd f ι)] : IsProper (j₀ ι j q ≫ pullback.snd q ι) := by
  have h1 : IsProper (pullback.snd (π ≫ f) ι) := by
    have : IsProper ((pullbackRightPullbackFstIso f ι π).hom ≫ pullback.snd (π ≫ f) ι) := by
      rw [pullbackRightPullbackFstIso_hom_snd]; infer_instance
    exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mp this
  have h2 : IsProper (pullback.snd (j ≫ q) ι) := by
    have : (pullback.congrHom hcomm rfl).hom ≫ pullback.snd (π ≫ f) ι = pullback.snd (j ≫ q) ι := by
      rw [pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
    rw [← this]; infer_instance
  have h3 : j₀ ι j q ≫ pullback.snd q ι =
      (pullbackRightPullbackFstIso q ι j).hom ≫ pullback.snd (j ≫ q) ι := by
    rw [pullbackRightPullbackFstIso_hom_snd]
  rw [h3]; infer_instance

omit [IsLocalRing A] [IsClosedImmersion ι] [Surjective π] [IsOpenImmersion j] in
include hcomm in
lemma isProper_j₀ [IsProper (pullback.snd f ι)] : IsProper (j₀ ι j q) :=
  have : IsProper (j₀ ι j q ≫ pullback.snd q ι) :=
    isProper_j₀_comp f ι π j q hcomm
  IsProper.of_comp (j₀ ι j q) (pullback.snd q ι)

omit [IsLocalRing A] [IsClosedImmersion ι] [IsProper q] in
lemma isClopen_range_j₀ (hp : IsProper (j₀ ι j q)) : IsClopen (Set.range (j₀ ι j q)) := by
  refine ⟨?_, ?_⟩
  · have : IsProper (j₀ ι j q) := hp
    exact (j₀ ι j q).isClosedMap.isClosed_range
  · rw [Scheme.Pullback.range_snd]
    exact (IsOpenImmersion.isOpen_range j).preimage (pP ι q).continuous

variable (V : Set P) (hV : IsClopen V) (hVfib : pP ι q ⁻¹' V = Set.range (j₀ ι j q))
include ι q hV hVfib

omit [IsProper π] [Surjective π] in
lemma subset_range_j : V ⊆ Set.range j := by
  intro v hv
  by_contra hvj
  have hW : IsClosed (V ∩ (Set.range j)ᶜ) :=
    hV.1.inter (IsOpenImmersion.isOpen_range j).isClosed_compl
  obtain ⟨w', ⟨hw'V, hw'j⟩, hqw'⟩ := exists_mem_of_isClosed ι q hW ⟨hv, hvj⟩
  have hw'range : w' ∈ Set.range (pP ι q) := by
    rw [Scheme.Pullback.range_fst]; exact hqw'
  obtain ⟨y, rfl⟩ := hw'range
  have hy : y ∈ pP ι q ⁻¹' V := hw'V
  rw [hVfib, Scheme.Pullback.range_snd] at hy
  exact hw'j hy

/-- The inverse image of the lifted clopen subset. -/
def Zop : X'.Opens := ⟨j ⁻¹' V, hV.2.preimage j.continuous⟩

omit ι q hVfib [IsOpenImmersion j] in
lemma isClosed_Zop : IsClosed (Zop j V hV : Set X') := hV.1.preimage j.continuous

lemma image_Zop : j '' (Zop j V hV : Set X') = V :=
  Set.image_preimage_eq_of_subset (subset_range_j ι j q V hV hVfib)

lemma isProper_Zop : IsProper ((Zop j V hV).ι ≫ j ≫ q) := by
  have hrange : Set.range ((Zop j V hV).ι ≫ j) = V := by
    change Set.range (j ∘ (Zop j V hV).ι) = V
    rw [Set.range_comp, Scheme.Opens.range_ι]
    exact image_Zop ι j q V hV hVfib
  have : IsClosedImmersion ((Zop j V hV).ι ≫ j) :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [hrange]; exact hV.1)
  rw [← Category.assoc]; infer_instance

omit [IsLocalRing A] [IsClosedImmersion ι]
  [IsProper π] [Surjective π] [IsOpenImmersion j] [IsProper q] in
include hcomm in
lemma mem_Zop_of {z : X'} (hz : (π ≫ f) z ∈ Set.range ι) : z ∈ (Zop j V hV : Set X') := by
  change j z ∈ V
  have hjz : j z ∈ Set.range (pP ι q) := by
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, ← Scheme.Hom.comp_apply, hcomm]; exact hz
  obtain ⟨y, hy⟩ := hjz
  have : y ∈ pP ι q ⁻¹' V := by
    rw [hVfib, Scheme.Pullback.range_snd]; exact ⟨z, hy.symm⟩
  rw [← hy]; exact this

lemma isClosed_image_j {C : Set X'} (hC : IsClosed C) (hCZ : C ⊆ (Zop j V hV : Set X')) :
    IsClosed (j '' C) := by
  have heq : j '' C = V ∩ (j '' Cᶜ)ᶜ := by
    ext c
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨hCZ hz, ?_⟩
      rintro ⟨z', hz', hzz'⟩
      exact hz' (j.isOpenEmbedding.injective hzz' ▸ hz)
    · rintro ⟨hcV, hc⟩
      obtain ⟨z, rfl⟩ := subset_range_j ι j q V hV hVfib hcV
      refine ⟨z, ?_, rfl⟩
      by_contra hz
      exact hc ⟨z, hz, rfl⟩
  rw [heq]
  exact hV.1.inter (j.isOpenEmbedding.isOpenMap _ hC.isOpen_compl).isClosed_compl

omit [Surjective π] in
include hcomm in
lemma disjoint_images :
    Disjoint (π '' (Zop j V hV : Set X')) (π '' (Zop j V hV : Set X')ᶜ) := by
  rw [Set.disjoint_left]
  rintro x ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, hx⟩
  have hC1Z : closure {z₁} ⊆ (Zop j V hV : Set X') :=
    (isClosed_Zop j V hV).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr
      hz₁)
  have hcl : IsClosed (j '' closure {z₁}) := isClosed_image_j ι j q V hV hVfib
    isClosed_closure hC1Z
  obtain ⟨w, ⟨z₁', hz₁', rfl⟩, hqw⟩ :=
    exists_mem_of_isClosed ι q hcl ⟨z₁, subset_closure rfl, rfl⟩
  have hc : π z₁' ∈ closure {π z₁} := by
    rw [← Set.image_singleton]
    exact image_closure_subset_closure_image π.continuous ⟨z₁', hz₁', rfl⟩
  have hcs : f (π z₁') ∈ Set.range ι := by
    rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply]; exact hqw
  have hsub : closure {π z₁} ⊆ π '' closure {z₂} :=
    (π.isClosedMap _ isClosed_closure).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr ⟨z₂, subset_closure rfl, hx⟩)
  obtain ⟨z₂', hz₂', hzz⟩ := hsub hc
  have hz₂'Z : z₂' ∉ (Zop j V hV : Set X') := by
    have : closure {z₂} ⊆ (Zop j V hV : Set X')ᶜ :=
      (Zop j V hV).isOpen.isClosed_compl.closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hz₂)
    exact this hz₂'
  apply hz₂'Z
  apply mem_Zop_of f ι π j q hcomm V hV hVfib
  rw [Scheme.Hom.comp_apply, hzz]; exact hcs

/-- The descended open subset obtained from the proper modification. -/
def Uop : X.Opens :=
  ⟨(π '' (Zop j V hV : Set X')ᶜ)ᶜ,
    (π.isClosedMap _ (Zop j V hV).isOpen.isClosed_compl).isOpen_compl⟩

include hcomm in
lemma coe_Uop_eq : (Uop π j V hV : Set X) = π '' (Zop j V hV : Set X') := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, rfl⟩ := π.surjective x
    by_cases hz : z ∈ (Zop j V hV : Set X')
    · exact ⟨z, hz, rfl⟩
    · exact absurd ⟨z, hz, rfl⟩ hx
  · intro hx hx'
    exact Set.disjoint_left.mp (disjoint_images f ι π j q hcomm V hV hVfib) hx hx'

include hcomm in
lemma isClosed_Uop : IsClosed (Uop π j V hV : Set X) := by
  rw [coe_Uop_eq f ι π j q hcomm V hV hVfib]
  exact π.isClosedMap _ (isClosed_Zop j V hV)

omit [IsLocalRing A] [IsClosedImmersion ι]
  [Surjective π] [IsOpenImmersion j] [IsProper q] in
include hcomm in
lemma range_fst_subset_Uop : Set.range (pullback.fst f ι) ⊆ (Uop π j V hV : Set X) := by
  rintro x hx ⟨z, hz, rfl⟩
  rw [Scheme.Pullback.range_fst] at hx
  exact hz (mem_Zop_of f ι π j q hcomm V hV hVfib (by rw [Scheme.Hom.comp_apply]; exact hx))

/-- The modification restricted to the descended open subset. -/
noncomputable def πU : (Zop j V hV).toScheme ⟶ (Uop π j V hV).toScheme :=
  IsOpenImmersion.lift (Uop π j V hV).ι ((Zop j V hV).ι ≫ π) (by
    change Set.range (π ∘ (Zop j V hV).ι) ⊆ Set.range (Uop π j V hV).ι
    rw [Scheme.Opens.range_ι, coe_Uop_eq f ι π j q hcomm V hV hVfib,
      Set.range_comp, Scheme.Opens.range_ι])

lemma πU_fac : πU f ι π j q hcomm V hV hVfib ≫ (Uop π j V hV).ι = (Zop j V hV).ι ≫ π :=
  IsOpenImmersion.lift_fac _ _ _

lemma surjective_πU : Surjective (πU f ι π j q hcomm V hV hVfib) := by
  refine ⟨fun u => ?_⟩
  have hu : (Uop π j V hV).ι u ∈ (Uop π j V hV : Set X) := by
    rw [← Scheme.Opens.range_ι]; exact ⟨u, rfl⟩
  rw [coe_Uop_eq f ι π j q hcomm V hV hVfib] at hu
  obtain ⟨z, hz, hzu⟩ := hu
  obtain ⟨w, rfl⟩ : z ∈ Set.range (Zop j V hV).ι := by rw [Scheme.Opens.range_ι]; exact hz
  refine ⟨w, (Uop π j V hV).ι.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, πU_fac f ι π j q hcomm V hV hVfib, Scheme.Hom.comp_apply, hzu]

variable [IsSeparated f] [LocallyOfFiniteType f] in
include hcomm in
lemma isProper_Uop : IsProper ((Uop π j V hV).ι ≫ f) := by
  have h1 : IsProper (πU f ι π j q hcomm V hV hVfib ≫ (Uop π j V hV).ι ≫ f) := by
    rw [← Category.assoc, πU_fac f ι π j q hcomm V hV hVfib, Category.assoc, ← hcomm]
    exact isProper_Zop ι j q V hV hVfib
  have : Surjective (πU f ι π j q hcomm V hV hVfib) :=
    surjective_πU f ι π j q hcomm V hV hVfib
  have h2 : UniversallyClosed ((Uop π j V hV).ι ≫ f) :=
    UniversallyClosed.of_comp_surjective (πU f ι π j q hcomm V hV hVfib) _
  exact ⟨⟩

end Main

end ProperClopenNbhd

end SchemeTheory.Properness.ProperClopenNeighborhoods

namespace AlgebraicGeometry

universe u
open CategoryTheory CategoryTheory.Limits
open SchemeTheory.Properness.ProperClopenNeighborhoods in
theorem exists_opens_isClosed_isProper_of_isProper_pullback_snd_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {K : Type u} [Field K] (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A))
    [IsClosedImmersion ι] [IsProper (pullback.snd f ι)] :
    ∃ U : X.Opens, IsClosed (U : Set X) ∧ IsProper (U.ι ≫ f) ∧
      Set.range (pullback.fst f ι) ⊆ (U : Set X) := by
  obtain ⟨X', P, π, j, q, hπ, hπs, hj, hq, hcomm⟩ :=
    AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated f
  have hp := ProperClopenNbhd.isProper_j₀ f ι π j q hcomm
  obtain ⟨V, hV, hVfib⟩ :=
    AlgebraicGeometry.exists_isClopen_preimage_eq_of_isProper_of_isAdicComplete q ι
      (Set.range (ProperClopenNbhd.j₀ ι j q)) (ProperClopenNbhd.isClopen_range_j₀ ι j q hp)
  exact ⟨ProperClopenNbhd.Uop π j V hV, ProperClopenNbhd.isClosed_Uop f ι π j q hcomm V hV hVfib,
    ProperClopenNbhd.isProper_Uop f ι π j q hcomm V hV hVfib,
    ProperClopenNbhd.range_fst_subset_Uop f ι π j q hcomm V hV hVfib⟩

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_isProper_of_isProper_pullback_snd_of_geometricallyConnected_of_isLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.Properness.ProperClosedFiber

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace IsProperOfProperClosedFibre

section ClosedPointOfField

variable {R : Type u} [CommRing R] {K : Type u} [Field K]
  (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion ι]

/-- The ring homomorphism defining the affine closed immersion. -/
noncomputable def ringHomOf : R →+* K := (Spec.preimage ι).hom

omit [IsClosedImmersion ι] in
lemma specMap_ringHomOf : Spec.map (CommRingCat.ofHom (ringHomOf ι)) = ι := by
  exact Spec.map_preimage ι

lemma surjective_ringHomOf : Function.Surjective (ringHomOf ι) :=
  SchemeTheory.Properness.CompleteBaseComponents.SolPiGeo.surjective_preimage ι

lemma ker_ringHomOf_isMaximal : (RingHom.ker (ringHomOf ι)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (surjective_ringHomOf ι)

lemma ker_ringHomOf_eq [IsLocalRing R] : RingHom.ker (ringHomOf ι) = maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal (ker_ringHomOf_isMaximal ι)

end ClosedPointOfField

section Completion

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Completion at the maximal ideal of the local base ring. -/
abbrev Rhat : Type u := AdicCompletion (maximalIdeal R) R

scoped instance [IsNoetherianRing R] : IsNoetherianRing (Rhat R) :=
  AdicCompletion.isNoetherianRing_of_isNoetherianRing _

scoped instance [IsNoetherianRing R] : Module.FaithfullyFlat R (Rhat R) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The canonical morphism from the completed local base. -/
noncomputable abbrev cmap : Spec (CommRingCat.of (Rhat R)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Rhat R)))

lemma flat_and_surjective_cmap [IsNoetherianRing R] : Flat (cmap R) ∧ Surjective (cmap R) := by
  rw [flat_and_surjective_SpecMap_iff]
  change (algebraMap R (Rhat R)).FaithfullyFlat
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  infer_instance

scoped instance [IsNoetherianRing R] : Flat (cmap R) := (flat_and_surjective_cmap R).1
scoped instance [IsNoetherianRing R] : Surjective (cmap R) := (flat_and_surjective_cmap R).2

variable {R}
variable {K : Type u} [Field K]
  (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion ι]

/-- The extension of the closed-point map to the completed base. -/
noncomputable def ghat : Rhat R →+* K :=
  (Ideal.Quotient.lift (maximalIdeal R ^ 1) (ringHomOf ι) (fun a ha => by
      rw [pow_one, ← ker_ringHomOf_eq ι] at ha; exact ha)).comp
    (AdicCompletion.evalₐ (maximalIdeal R) 1).toRingHom

lemma ghat_comp_algebraMap : (ghat ι).comp (algebraMap R (Rhat R)) = ringHomOf ι := by
  ext a
  simp only [ghat, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, AdicCompletion.evalₐ_algebraMap]
  rfl

lemma surjective_ghat : Function.Surjective (ghat ι) := by
  intro y
  obtain ⟨a, rfl⟩ := surjective_ringHomOf ι y
  exact ⟨algebraMap R (Rhat R) a, by rw [← ghat_comp_algebraMap ι]; rfl⟩

/-- The closed-point immersion into the completed base. -/
noncomputable abbrev ιhat : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (Rhat R)) :=
  Spec.map (CommRingCat.ofHom (ghat ι))

scoped instance : IsClosedImmersion (ιhat ι) :=
  IsClosedImmersion.spec_of_surjective _ (surjective_ghat ι)

lemma ιhat_comp_cmap : ιhat ι ≫ cmap R = ι := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ghat_comp_algebraMap, specMap_ringHomOf]

lemma ιhat_apply [IsNoetherianRing R] (z : Spec (CommRingCat.of K)) :
    (ιhat ι) z = closedPoint (Rhat R) := by
  apply PrimeSpectrum.ext
  change Ideal.comap (ghat ι) z.asIdeal = maximalIdeal (Rhat R)
  have hz : z.asIdeal = ⊥ := by
    exact (Ideal.eq_bot_or_top z.asIdeal).resolve_right z.isPrime.ne_top
  rw [hz, ← RingHom.ker_eq_comap_bot]
  exact IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (surjective_ghat ι))

lemma closedPoint_mem_range_ιhat [IsNoetherianRing R] : closedPoint (Rhat R) ∈ Set.range (ιhat ι) :=
  ⟨closedPoint K, ιhat_apply ι _⟩

end Completion

section Main

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [GeometricallyConnected f]
  (e : Spec (CommRingCat.of R) ⟶ X) (he : e ≫ f = 𝟙 (Spec (CommRingCat.of R)))
  {K : Type u} [Field K] (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
  [IsClosedImmersion ι] [IsProper (pullback.snd f ι)]

/-- The structure morphism after completion of the base. -/
noncomputable abbrev fhat : pullback f (cmap R) ⟶ Spec (CommRingCat.of (Rhat R)) :=
  pullback.snd f (cmap R)

/-- The section after completion of the base. -/
noncomputable def ehat : Spec (CommRingCat.of (Rhat R)) ⟶ pullback f (cmap R) :=
  pullback.lift (cmap R ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])

omit [IsNoetherianRing R] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f] [GeometricallyConnected f] in
@[scoped simp] lemma ehat_fhat : ehat f e he ≫ fhat f = 𝟙 _ := pullback.lift_snd _ _ _

scoped instance isProper_fibre_hat : IsProper (pullback.snd (fhat f) (ιhat ι)) := by
  let i₁ : pullback (fhat f) (ιhat ι) ≅ pullback f (ιhat ι ≫ cmap R) :=
    pullbackLeftPullbackSndIso f (cmap R) (ιhat ι)
  let i₂ : pullback f (ιhat ι ≫ cmap R) ≅ pullback f ι :=
    pullback.congrHom rfl (ιhat_comp_cmap ι)
  have h : (i₁ ≪≫ i₂).hom ≫ pullback.snd f ι = pullback.snd (fhat f) (ιhat ι) := by
    rw [Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_snd,
      Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  rw [← h]
  infer_instance

include e he ι in
lemma isProper_fhat : IsProper (fhat f) := by
  obtain ⟨U, hUcl, hUprop, hUfib⟩ :=
    AlgebraicGeometry.exists_opens_isClosed_isProper_of_isProper_pullback_snd_of_isAdicComplete
      (fhat f) (ιhat ι)
  let z : Spec (CommRingCat.of (Rhat R)) := closedPoint (Rhat R)
  have hsec : ∀ y, ehat f e he y ∈ (U : Set _) := by
    have hcp : ehat f e he z ∈ (U : Set _) := by
      apply hUfib
      rw [Scheme.Pullback.range_fst]
      change (ehat f e he ≫ fhat f) z ∈ Set.range (ιhat ι)
      rw [ehat_fhat]
      exact closedPoint_mem_range_ιhat ι
    intro y
    have hy : y ⤳ z := IsLocalRing.specializes_closedPoint y
    exact (hy.map (ehat f e he).continuous).mem_open U.isOpen hcp
  have hU : U = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hconn := (fhat f).isConnected_preimage_singleton (fhat f x)
    have hsub : (fhat f) ⁻¹' {fhat f x} ⊆ (U : Set _) :=
      hconn.isPreconnected.subset_isClopen ⟨hUcl, U.isOpen⟩
        ⟨ehat f e he (fhat f x), by
          change fhat f (ehat f e he _) = _
          rw [← Scheme.Hom.comp_apply, ehat_fhat]; rfl, hsec _⟩
    exact hsub rfl
  subst hU
  have h2 : (pullback f (cmap R)).topIso.hom ≫ fhat f = (⊤ : (pullback f (cmap R)).Opens).ι ≫ fhat
    f := by
    rw [Scheme.topIso_hom]
  rw [← h2] at hUprop
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mp hUprop

include e he ι in
theorem isProper : IsProper f := by
  have h1 : UniversallyClosed (fhat f) := by
    have : IsProper (fhat f) := isProper_fhat f e he ι
    infer_instance
  have h2 : UniversallyClosed f :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := f) (g := cmap R)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h1
  exact ⟨⟩

end Main

end IsProperOfProperClosedFibre

end SchemeTheory.Properness.ProperClosedFiber

namespace AlgebraicGeometry

universe u
open CategoryTheory CategoryTheory.Limits
open SchemeTheory.Properness.ProperClosedFiber in
theorem isProper_of_isProper_pullback_snd_of_geometricallyConnected_of_isLocalRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [GeometricallyConnected f]
    (e : Spec (CommRingCat.of R) ⟶ X) (he : e ≫ f = 𝟙 (Spec (CommRingCat.of R)))
    {K : Type u} [Field K] (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    [IsClosedImmersion ι] [IsProper (pullback.snd f ι)] :
    IsProper f :=
  IsProperOfProperClosedFibre.isProper f e he ι

end AlgebraicGeometry
end
