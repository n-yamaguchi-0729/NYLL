/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.EndDegree
public import Nyll.AbelianVarieties.Geometry.GroupLaw
public import Nyll.AbelianVarieties.Geometry.Quotients.Descent
public import Nyll.AbelianVarieties.NeronModels.Endomorphisms
public import Nyll.SchemeTheory.Etale.Neighborhoods
public import Nyll.SchemeTheory.Descent.GaloisClosedSubschemes
public import Nyll.AbelianVarieties.Basic
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Kernel
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.GeometricallyConnectedIdentityComponent
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawCompMulEqMulComp
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawSmoothOfRelativeDimension
public import Nyll.AlgebraicCurves.Geometry.Picard.CompEqOpenImmersion
public import Nyll.SchemeTheory.Morphisms.ReducedSmooth
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Galois traces and retractions onto proper subgroups

Descend the finite Galois trace of a torsor and use it to construct a retraction
onto a proper commutative subgroup, up to multiplication by a positive integer.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.GaloisTorsorTrace


noncomputable section

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

namespace TorsorConstruction
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian

variable {K : Type u} [Field K] {A : Scheme.{u}} {fA : A ⟶ Spec (CommRingCat.of K)}


/-- The finite product of points in the commutative relative group. -/
def bigProd (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) {ι : Type*} (s : Finset ι) (F : ι → SchemeHomOver t fA) :
    SchemeHomOver t fA :=
  @Finset.prod ι (SchemeHomOver t fA) (pointCommGroup LA hc t).toCommMonoid s F

theorem nsmul_eq_pow (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) (x : SchemeHomOver t fA) :
    LA.nsmul t n x = (let : CommGroup (SchemeHomOver t fA) := LA.pointCommGroup hc t; x ^ n) := by
  let : CommGroup (SchemeHomOver t fA) := LA.pointCommGroup hc t
  induction n with
  | zero => rfl
  | succ n ih => rw [LA.nsmul_succ, pow_succ, ih]; rfl

theorem bigProd_natural (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (t' : T' ⟶ Spec (CommRingCat.of K)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') {ι : Type*} (s : Finset ι) (F : ι → SchemeHomOver t fA) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (bigProd LA hc t s F) =
      bigProd LA hc t' s (fun i => GoodReductionJacobian.schemeHomOverComp ψ hψ (F i)) := by
  let : CommGroup (SchemeHomOver t fA) := LA.pointCommGroup hc t
  let : CommGroup (SchemeHomOver t' fA) := LA.pointCommGroup hc t'
  let φ : SchemeHomOver t fA →* SchemeHomOver t' fA :=
    { toFun := GoodReductionJacobian.schemeHomOverComp ψ hψ
      map_one' := LA.one_natural t t' ψ hψ
      map_mul' := fun x y => LA.mul_natural t t' ψ hψ x y }
  exact map_prod φ F s

theorem bigProd_mul_left (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) {ι : Type*} [Fintype ι] (a : SchemeHomOver t fA)
    (F : ι → SchemeHomOver t fA) :
    bigProd LA hc t Finset.univ (fun i => LA.mul t a (F i)) =
      LA.mul t (bigProd LA hc t Finset.univ F) (LA.nsmul t (Fintype.card ι) a) := by
  let : CommGroup (SchemeHomOver t fA) := LA.pointCommGroup hc t
  rw [nsmul_eq_pow LA hc]
  change (∏ i, a * F i) = (∏ i, F i) * a ^ (Fintype.card ι)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, mul_comm]

theorem bigProd_equiv (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) {ι : Type*} [Fintype ι] (e : ι ≃ ι)
    (F G : ι → SchemeHomOver t fA) (h : ∀ i, F i = G (e i)) :
    bigProd LA hc t Finset.univ F = bigProd LA hc t Finset.univ G := by
  let : CommGroup (SchemeHomOver t fA) := LA.pointCommGroup hc t
  exact Fintype.prod_equiv e F G h

theorem bigProd_congr (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) {ι : Type*} (s : Finset ι)
    (F G : ι → SchemeHomOver t fA) (h : ∀ i, F i = G i) :
    bigProd LA hc t s F = bigProd LA hc t s G := by
  let : CommGroup (SchemeHomOver t fA) := LA.pointCommGroup hc t
  exact Finset.prod_congr rfl fun i _ => h i

/-- A natural simply transitive action of the relative group. -/
structure TorsorData (LA : RelativeGroupLaw K fA) {V : Scheme.{u}}
    (g : V ⟶ Spec (CommRingCat.of K)) where
  /-- The action on points. -/
  act : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)),
    SchemeHomOver t fA → SchemeHomOver t g → SchemeHomOver t g
  /-- Naturality under change of the test scheme. -/
  act_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (t' : T' ⟶ Spec (CommRingCat.of K)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (a : SchemeHomOver t fA) (v : SchemeHomOver t g),
    GoodReductionJacobian.schemeHomOverComp ψ hψ (act t a v) =
      act t' (GoodReductionJacobian.schemeHomOverComp ψ hψ a)
        (GoodReductionJacobian.schemeHomOverComp ψ hψ v)
  /-- Compatibility with multiplication. -/
  act_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (a b : SchemeHomOver t fA) (v : SchemeHomOver t g),
    act t (LA.mul t a b) v = act t a (act t b v)
  /-- Existence and uniqueness of translating points. -/
  act_torsor : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (v w : SchemeHomOver t g),
    ∃! a : SchemeHomOver t fA, act t a v = w

namespace TorsorData

variable {LA : RelativeGroupLaw K fA} {V : Scheme.{u}} {g : V ⟶ Spec (CommRingCat.of K)}
  (D : TorsorData LA g)

/-- The unique translating point carrying the second torsor point to the first. -/
def delta {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (v w : SchemeHomOver t g) :
    SchemeHomOver t fA :=
  (D.act_torsor t w v).choose

theorem act_delta {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (v w : SchemeHomOver t g) :
    D.act t (D.delta t v w) w = v :=
  (D.act_torsor t w v).choose_spec.1

theorem delta_unique {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (v w : SchemeHomOver t g)
    (a : SchemeHomOver t fA) (ha : D.act t a w = v) : a = D.delta t v w :=
  (D.act_torsor t w v).unique ha (D.act_delta t v w)

theorem delta_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (t' : T' ⟶ Spec (CommRingCat.of K)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (v w : SchemeHomOver t g) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (D.delta t v w) =
      D.delta t' (GoodReductionJacobian.schemeHomOverComp ψ hψ v)
        (GoodReductionJacobian.schemeHomOverComp ψ hψ w) := by
  apply D.delta_unique
  rw [← D.act_natural, D.act_delta]

theorem delta_act {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (a : SchemeHomOver t fA)
    (v w : SchemeHomOver t g) :
    D.delta t (D.act t a v) w = LA.mul t a (D.delta t v w) := by
  symm
  apply D.delta_unique
  rw [D.act_mul, D.act_delta]

end TorsorData

section Galois

variable (K' : Type u) [Field K'] [Algebra K K']

/-- The spectrum map for the base field extension. -/
abbrev baseExt (K : Type u) [Field K] (K' : Type u) [Field K'] [Algebra K K'] :
    Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K K'))

/-- The spectrum automorphism induced by a field automorphism. -/
abbrev specAut {K : Type u} [Field K] {K' : Type u} [Field K'] [Algebra K K'] (σ : K' ≃ₐ[K] K') :
    Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K') :=
  Spec.map (CommRingCat.ofHom ((σ : K' →ₐ[K] K') : K' →+* K'))

theorem specAut_comp_baseExt (σ : K' ≃ₐ[K] K') : specAut σ ≫ baseExt K K' = baseExt K K' := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact σ.commutes x

theorem specAut_mul (σ τ : K' ≃ₐ[K] K') : specAut (τ * σ) = specAut τ ≫ specAut σ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

variable {K'}
variable {V : Scheme.{u}} {g : V ⟶ Spec (CommRingCat.of K)}
  (P : Spec (CommRingCat.of K') ⟶ V) (hP : P ≫ g = baseExt K K')

/-- A conjugate of the chosen torsor point. -/
def conjPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (t' : T ⟶ Spec (CommRingCat.of K'))
    (ht : t' ≫ baseExt K K' = t) (σ : K' ≃ₐ[K] K') : SchemeHomOver t g :=
  ⟨t' ≫ specAut σ ≫ P, by rw [Category.assoc, Category.assoc, hP, specAut_comp_baseExt, ht]⟩

@[scoped simp]
theorem conjPt_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (t' : T ⟶ Spec
  (CommRingCat.of K'))
    (ht : t' ≫ baseExt K K' = t) (σ : K' ≃ₐ[K] K') :
    (conjPt P hP t t' ht σ).1 = t' ≫ specAut σ ≫ P := rfl

theorem conjPt_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (t₂ : T' ⟶ Spec (CommRingCat.of K)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t₂)
    (t' : T ⟶ Spec (CommRingCat.of K')) (ht : t' ≫ baseExt K K' = t) (σ : K' ≃ₐ[K] K') :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (conjPt P hP t t' ht σ) =
      conjPt P hP t₂ (ψ ≫ t') (by rw [Category.assoc, ht, hψ]) σ :=
  Subtype.ext (by
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, conjPt_coe, Category.assoc])

theorem conjPt_twist {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (t' : T ⟶ Spec (CommRingCat.of K')) (τ : K' ≃ₐ[K] K')
    (ht : (t' ≫ specAut τ) ≫ baseExt K K' = t) (ht' : t' ≫ baseExt K K' = t) (σ : K' ≃ₐ[K] K') :
    conjPt P hP t (t' ≫ specAut τ) ht σ = conjPt P hP t t' ht' (τ * σ) :=
  Subtype.ext (by
    simp only [conjPt_coe, specAut_mul, Category.assoc])

variable (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative) (D : TorsorData LA g)
  [FiniteDimensional K K']

/-- The product of all Galois conjugate displacement points. -/
def Psi {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (t' : T ⟶ Spec (CommRingCat.of K'))
    (ht : t' ≫ baseExt K K' = t) (v : SchemeHomOver t g) : SchemeHomOver t fA :=
  bigProd LA hc t Finset.univ (fun σ : K' ≃ₐ[K] K' => D.delta t v (conjPt P hP t t' ht σ))

theorem Psi_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (t₂ : T' ⟶ Spec (CommRingCat.of K)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t₂)
    (t' : T ⟶ Spec (CommRingCat.of K')) (ht : t' ≫ baseExt K K' = t) (v : SchemeHomOver t g) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (Psi P hP LA hc D t t' ht v) =
      Psi P hP LA hc D t₂ (ψ ≫ t') (by rw [Category.assoc, ht, hψ])
        (GoodReductionJacobian.schemeHomOverComp ψ hψ v) := by
  unfold Psi
  rw [bigProd_natural]
  refine bigProd_congr LA hc t₂ _ _ _ fun σ => ?_
  rw [D.delta_natural, conjPt_natural]

theorem Psi_congr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    {t'₁ t'₂ : T ⟶ Spec (CommRingCat.of K')} (e : t'₁ = t'₂)
    (h₁ : t'₁ ≫ baseExt K K' = t) (h₂ : t'₂ ≫ baseExt K K' = t)
    {v₁ v₂ : SchemeHomOver t g} (ev : v₁.1 = v₂.1) :
    Psi P hP LA hc D t t'₁ h₁ v₁ = Psi P hP LA hc D t t'₂ h₂ v₂ := by
  subst e
  cases Subtype.ext ev
  rfl

theorem Psi_twist {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (t' : T ⟶ Spec (CommRingCat.of K')) (τ : K' ≃ₐ[K] K')
    (ht : (t' ≫ specAut τ) ≫ baseExt K K' = t) (ht' : t' ≫ baseExt K K' = t) (v : SchemeHomOver t
      g) :
    Psi P hP LA hc D t (t' ≫ specAut τ) ht v = Psi P hP LA hc D t t' ht' v := by
  unfold Psi
  refine bigProd_equiv LA hc t (Equiv.mulLeft τ) _ _ fun σ => ?_
  rw [conjPt_twist P hP t t' τ ht ht']
  rfl

theorem Psi_act {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (t' : T ⟶ Spec (CommRingCat.of K')) (ht : t' ≫ baseExt K K' = t)
    (a : SchemeHomOver t fA) (v : SchemeHomOver t g) :
    Psi P hP LA hc D t t' ht (D.act t a v) =
      LA.mul t (Psi P hP LA hc D t t' ht v) (LA.nsmul t (Fintype.card (K' ≃ₐ[K] K')) a) := by
  unfold Psi
  rw [← bigProd_mul_left]
  refine bigProd_congr LA hc t _ _ _ fun σ => ?_
  rw [D.delta_act]

end Galois

section Descent

variable (K' : Type u) [Field K'] [Algebra K K'] [FiniteDimensional K K']
  (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative)
  {V : Scheme.{u}} {g : V ⟶ Spec (CommRingCat.of K)} (D : TorsorData LA g)
  (P : Spec (CommRingCat.of K') ⟶ V) (hP : P ≫ g = baseExt K K')

/-- The structural map of the base-changed torsor to the original field. -/
abbrev tV : pullback g (baseExt K K') ⟶ Spec (CommRingCat.of K) :=
  pullback.snd g (baseExt K K') ≫ baseExt K K'

/-- The universal point of the torsor after field extension. -/
def vpt : SchemeHomOver (tV K' (g := g)) g :=
  ⟨pullback.fst g (baseExt K K'), pullback.condition⟩

/-- The Galois trace point on the base-changed torsor. -/
def psiPt : SchemeHomOver (tV K' (g := g)) fA :=
  Psi P hP LA hc D (tV K') (pullback.snd g (baseExt K K')) rfl (vpt K')

/-- The morphism represented by the trace point after field extension. -/
def fK : pullback g (baseExt K K') ⟶ pullback fA (baseExt K K') :=
  pullback.lift (psiPt K' LA hc D P hP).1 (pullback.snd g (baseExt K K')) (psiPt K' LA hc D P hP).2

@[reassoc]
theorem fK_fst : fK K' LA hc D P hP ≫ pullback.fst fA (baseExt K K') = (psiPt K' LA hc D P hP).1 :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem fK_snd : fK K' LA hc D P hP ≫ pullback.snd fA (baseExt K K') = pullback.snd g (baseExt K
  K') :=
  pullback.lift_snd _ _ _

theorem comp_psiPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x : T ⟶ pullback g (baseExt K K')) (hx : x ≫ tV K' = t) :
    x ≫ (psiPt K' LA hc D P hP).1 =
      (Psi P hP LA hc D t (x ≫ pullback.snd g (baseExt K K')) (by rw [Category.assoc]; exact hx)
        ⟨x ≫ pullback.fst g (baseExt K K'), by
          rw [Category.assoc, pullback.condition]; exact hx⟩).1 := by
  have h := congrArg Subtype.val
    (Psi_natural P hP LA hc D (tV K') t x hx (pullback.snd g (baseExt K K')) rfl (vpt K'))
  exact h

theorem twist_comp_fK (σ : K' ≃ₐ[K] K') (hσ : specAut σ ≫ baseExt K K' = baseExt K K') :
    pullback.map g (baseExt K K') g (baseExt K K') (𝟙 V) (specAut σ) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hσ]) ≫ fK K' LA hc
          D P hP =
      fK K' LA hc D P hP ≫ pullback.map fA (baseExt K K') fA (baseExt K K') (𝟙 A) (specAut σ) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hσ]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, fK_fst, Category.comp_id]
    have hx : pullback.map g (baseExt K K') g (baseExt K K') (𝟙 V) (specAut σ) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hσ]) ≫ tV K' = tV
          K' := by
      rw [← Category.assoc, pullback.lift_snd, Category.assoc, hσ]
    rw [comp_psiPt K' LA hc D P hP (tV K') _ hx]
    have e : pullback.map g (baseExt K K') g (baseExt K K') (𝟙 V) (specAut σ) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hσ]) ≫
          pullback.snd g (baseExt K K') = pullback.snd g (baseExt K K') ≫ specAut σ :=
      pullback.lift_snd _ _ _
    have hs : (pullback.snd g (baseExt K K') ≫ specAut σ) ≫ baseExt K K' = tV K' := by
      rw [Category.assoc, hσ]
    rw [congrArg Subtype.val (Psi_congr P hP LA hc D (tV K') e _ hs (v₂ := vpt K')
      (by change _ ≫ pullback.fst g (baseExt K K') = pullback.fst g (baseExt K K')
          rw [pullback.lift_fst]; exact Category.comp_id _))]
    exact congrArg Subtype.val (Psi_twist P hP LA hc D (tV K') _ σ hs rfl (vpt K'))
  · simp only [Category.assoc, pullback.lift_snd, fK_snd, fK_snd_assoc]

theorem comp_eq_Psi (φ : V ⟶ A)
    (hφ' : (psiPt K' LA hc D P hP).1 = pullback.fst g (baseExt K K') ≫ φ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (t' : T ⟶ Spec (CommRingCat.of K'))
    (ht : t' ≫ baseExt K K' = t) (w : SchemeHomOver t g) :
    w.1 ≫ φ = (Psi P hP LA hc D t t' ht w).1 := by
  let x : T ⟶ pullback g (baseExt K K') := pullback.lift w.1 t' (by rw [w.2, ht])
  have hx : x ≫ tV K' = t := by rw [← Category.assoc, pullback.lift_snd, ht]
  calc w.1 ≫ φ = (x ≫ pullback.fst g (baseExt K K')) ≫ φ := by rw [pullback.lift_fst]
    _ = x ≫ (psiPt K' LA hc D P hP).1 := by rw [Category.assoc, ← hφ']
    _ = _ := comp_psiPt K' LA hc D P hP t x hx
    _ = (Psi P hP LA hc D t t' ht w).1 :=
        congrArg Subtype.val (Psi_congr P hP LA hc D t (pullback.lift_snd _ _ _) _ ht
          (pullback.lift_fst _ _ _))

variable [IsGalois K K'] [IsSeparated fA] [LocallyOfFiniteType fA]

theorem exists_descent :
    ∃ (φ : V ⟶ A), φ ≫ fA = g ∧
      (psiPt K' LA hc D P hP).1 = pullback.fst g (baseExt K K') ≫ φ := by
  obtain ⟨φ, hφ, hf, -⟩ :=
    exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq_of_finiteDimensional
      K K' V A g fA (fK K' LA hc D P hP) (fK_snd K' LA hc D P hP)
      (fun σ hσ => twist_comp_fK K' LA hc D P hP σ hσ)
  refine ⟨φ, hφ, ?_⟩
  rw [← fK_fst, hf, pullback.lift_fst]

end Descent

theorem exists_hom (K' : Type u) [Field K'] [Algebra K K'] [FiniteDimensional K K'] [IsGalois K K']
    [IsSeparated fA] [LocallyOfFiniteType fA]
    (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative)
    {V : Scheme.{u}} {g : V ⟶ Spec (CommRingCat.of K)} (D : TorsorData LA g)
    (P : Spec (CommRingCat.of K') ⟶ V) (hP : P ≫ g = baseExt K K') :
    ∃ φ : SchemeHomOver g fA,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (a : SchemeHomOver t fA)
        (v : SchemeHomOver t g),
        NeronModelInfra.schemeHomOverComp (D.act t a v) φ =
          LA.mul t (NeronModelInfra.schemeHomOverComp v φ)
            (LA.nsmul t (Module.finrank K K') a) := by
  obtain ⟨φ, hφ, hφ'⟩ := exists_descent K' LA hc D P hP
  refine ⟨⟨φ, hφ⟩, fun {T} t a v => ?_⟩
  have hcard : Fintype.card (K' ≃ₐ[K] K') = Module.finrank K K' := by
    rw [← Nat.card_eq_fintype_card]; exact IsGalois.card_aut_eq_finrank K K'
  apply Subtype.ext
  simp only [NeronModelInfra.schemeHomOverComp_coe]
  let p := pullback.fst t (baseExt K K')
  let t' := pullback.snd t (baseExt K K')
  have hp : t' ≫ baseExt K K' = p ≫ t := pullback.condition.symm
  rw [← cancel_epi p]
  have eL : p ≫ (D.act t a v).1 ≫ φ =
      (LA.mul (p ≫ t)
        (Psi P hP LA hc D (p ≫ t) t' hp (GoodReductionJacobian.schemeHomOverComp p rfl v))
        (LA.nsmul (p ≫ t) (Fintype.card (K' ≃ₐ[K] K'))
          (GoodReductionJacobian.schemeHomOverComp p rfl a))).1 := by
    have h1 : p ≫ (D.act t a v).1 =
        (D.act (p ≫ t) (GoodReductionJacobian.schemeHomOverComp p rfl a)
          (GoodReductionJacobian.schemeHomOverComp p rfl v)).1 :=
      congrArg Subtype.val (D.act_natural t (p ≫ t) p rfl a v)
    rw [← Category.assoc, h1, comp_eq_Psi K' LA hc D P hP φ hφ' (p ≫ t) t' hp, Psi_act]
  have eR : p ≫ (LA.mul t (NeronModelInfra.schemeHomOverComp v ⟨φ, hφ⟩)
        (LA.nsmul t (Module.finrank K K') a)).1 =
      (LA.mul (p ≫ t)
        (Psi P hP LA hc D (p ≫ t) t' hp (GoodReductionJacobian.schemeHomOverComp p rfl v))
        (LA.nsmul (p ≫ t) (Fintype.card (K' ≃ₐ[K] K'))
          (GoodReductionJacobian.schemeHomOverComp p rfl a))).1 := by
    have h1 := congrArg Subtype.val
      (LA.mul_natural t (p ≫ t) p rfl (NeronModelInfra.schemeHomOverComp v ⟨φ, hφ⟩)
        (LA.nsmul t (Module.finrank K K') a))
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at h1
    rw [h1, ← LA.nsmul_natural, hcard]
    have h2 : GoodReductionJacobian.schemeHomOverComp p rfl
        (NeronModelInfra.schemeHomOverComp v ⟨φ, hφ⟩) =
        Psi P hP LA hc D (p ≫ t) t' hp (GoodReductionJacobian.schemeHomOverComp p rfl v) := by
      apply Subtype.ext
      rw [GoodReductionJacobian.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe,
        ← Category.assoc]
      exact comp_eq_Psi K' LA hc D P hP φ hφ' (p ≫ t) t' hp
        (GoodReductionJacobian.schemeHomOverComp p rfl v)
    rw [h2]
  rw [eL, eR]

end TorsorConstruction

end
end AbelianVarieties.NOSProofs.GaloisTorsorTrace

namespace GoodReductionJacobian.RelativeGroupLaw
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AbelianVarieties.NOSProofs.GaloisTorsorTrace
universe u

theorem exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois
    (K : Type u) [Field K] {A : Scheme.{u}} (fA : A ⟶ Spec (CommRingCat.of K))
    [IsSeparated fA] [LocallyOfFiniteType fA]
    (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative)
    {V : Scheme.{u}} (g : V ⟶ Spec (CommRingCat.of K))
    (act : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)),
      SchemeHomOver t fA → SchemeHomOver t g → SchemeHomOver t g)
    (act_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (t' : T' ⟶ Spec (CommRingCat.of K)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
      (a : SchemeHomOver t fA) (v : SchemeHomOver t g),
      GoodReductionJacobian.schemeHomOverComp ψ hψ (act t a v) =
        act t' (GoodReductionJacobian.schemeHomOverComp ψ hψ a)
          (GoodReductionJacobian.schemeHomOverComp ψ hψ v))
    (act_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (a b : SchemeHomOver t fA) (v : SchemeHomOver t g),
      act t (LA.mul t a b) v = act t a (act t b v))
    (act_torsor : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (v w : SchemeHomOver t g),
      ∃! a : SchemeHomOver t fA, act t a v = w)
    (K' : Type u) [Field K'] [Algebra K K'] [FiniteDimensional K K'] [IsGalois K K']
    (P : Spec (CommRingCat.of K') ⟶ V) (hP : P ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K
      K'))) :
    ∃ φ : SchemeHomOver g fA,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (a : SchemeHomOver t fA)
        (v : SchemeHomOver t g),
        NeronModelInfra.schemeHomOverComp (act t a v) φ =
          LA.mul t (NeronModelInfra.schemeHomOverComp v φ) (LA.nsmul t (Module.finrank K K') a) :=
  TorsorConstruction.exists_hom K' LA hc ⟨act, act_natural, act_mul, act_torsor⟩ P hP

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_schemeHomOverComp_eq_nsmul_of_isProper_of_isCommutative_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.RosenlichtRetractions


noncomputable section

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

universe u

namespace RetractionConstruction
open _root_.GoodReductionJacobian.RelativeGroupLaw hiding action
open _root_.GoodReductionJacobian

section Calculus

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
  {fX : X ⟶ Spec (CommRingCat.of k)} {fY : Y ⟶ Spec (CommRingCat.of k)}
  {fZ : Z ⟶ Spec (CommRingCat.of k)}


open AbelianVarieties.NOSProofs.GaloisTorsorTrace.TorsorConstruction (nsmul_eq_pow)

theorem comp_eq_transition {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (x : SchemeHomOver t fX) (P : SchemeHomOver fX fY) :
    NeronModelInfra.schemeHomOverComp x P = GoodReductionJacobian.schemeHomOverComp x.1 x.2 P :=
  rfl

theorem comp_lawMul (LY : RelativeGroupLaw k fY) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t fX) (P Q : SchemeHomOver fX fY) :
    NeronModelInfra.schemeHomOverComp x (LY.mul fX P Q) =
      LY.mul t (NeronModelInfra.schemeHomOverComp x P) (NeronModelInfra.schemeHomOverComp x Q) := by
  rw [comp_eq_transition, LY.mul_natural fX t x.1 x.2 P Q]
  rfl

theorem comp_lawOne (LY : RelativeGroupLaw k fY) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t fX) :
    NeronModelInfra.schemeHomOverComp x (LY.one fX) = LY.one t := by
  rw [comp_eq_transition, LY.one_natural fX t x.1 x.2]

theorem comp_lawNsmul (LY : RelativeGroupLaw k fY) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t fX) (n : ℕ) (P : SchemeHomOver fX fY) :
    NeronModelInfra.schemeHomOverComp x (LY.nsmul fX n P) =
      LY.nsmul t n (NeronModelInfra.schemeHomOverComp x P) := by
  rw [comp_eq_transition, LY.nsmul_natural fX t x.1 x.2 n P]
  rfl

theorem comp_lawInv (LY : RelativeGroupLaw k fY) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t fX) (P : SchemeHomOver fX fY) :
    NeronModelInfra.schemeHomOverComp x (LY.inv fX P) =
      LY.inv t (NeronModelInfra.schemeHomOverComp x P) := by
  exact LY.inv_natural fX t x.1 x.2 P

/-- Compatibility of a relative morphism with multiplication. -/
def IsHom (LX : RelativeGroupLaw k fX) (LY : RelativeGroupLaw k fY) (φ : SchemeHomOver fX fY) :
    Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t fX),
    NeronModelInfra.schemeHomOverComp (LX.mul t x y) φ =
      LY.mul t (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)

namespace IsHom

variable {LX : RelativeGroupLaw k fX} {LY : RelativeGroupLaw k fY} {LZ : RelativeGroupLaw k fZ}

theorem one {φ : SchemeHomOver fX fY} (h : IsHom LX LY φ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) :
    NeronModelInfra.schemeHomOverComp (LX.one t) φ = LY.one t := by
  let : Group (SchemeHomOver t fY) := LY.pointGroup t
  have h1 := h t (LX.one t) (LX.one t)
  rw [LX.one_mul] at h1
  have : NeronModelInfra.schemeHomOverComp (LX.one t) φ *
      NeronModelInfra.schemeHomOverComp (LX.one t) φ =
      NeronModelInfra.schemeHomOverComp (LX.one t) φ := h1.symm
  exact mul_eq_left.mp this

theorem inv {φ : SchemeHomOver fX fY} (h : IsHom LX LY φ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t fX) :
    NeronModelInfra.schemeHomOverComp (LX.inv t x) φ =
      LY.inv t (NeronModelInfra.schemeHomOverComp x φ) := by
  let : Group (SchemeHomOver t fY) := LY.pointGroup t
  have h1 : LY.mul t (NeronModelInfra.schemeHomOverComp (LX.inv t x) φ)
      (NeronModelInfra.schemeHomOverComp x φ) = LY.one t := by
    rw [← h, LX.inv_mul_cancel, h.one]
  exact (inv_eq_of_mul_eq_one_left h1).symm

theorem nsmul {φ : SchemeHomOver fX fY} (h : IsHom LX LY φ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (n : ℕ) (x : SchemeHomOver t fX) :
    NeronModelInfra.schemeHomOverComp (LX.nsmul t n x) φ =
      LY.nsmul t n (NeronModelInfra.schemeHomOverComp x φ) := by
  induction n with
  | zero => exact h.one t
  | succ n ih => rw [LX.nsmul_succ, LY.nsmul_succ, h, ih]

theorem comp {φ : SchemeHomOver fX fY} {ψ : SchemeHomOver fY fZ} (h₁ : IsHom LX LY φ)
    (h₂ : IsHom LY LZ ψ) : IsHom LX LZ (NeronModelInfra.schemeHomOverComp φ ψ) := by
  intro T t x y
  rw [← NeronModelInfra.schemeHomOverComp_assoc, h₁, h₂, NeronModelInfra.schemeHomOverComp_assoc,
    NeronModelInfra.schemeHomOverComp_assoc]

end IsHom

theorem eq_of_comp_mono_eq (φ : SchemeHomOver fX fY) [Mono φ.1] {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} {x y : SchemeHomOver t fX}
    (hxy : NeronModelInfra.schemeHomOverComp x φ = NeronModelInfra.schemeHomOverComp y φ) :
    x = y := by
  have hval := congrArg Subtype.val hxy
  simp only [NeronModelInfra.schemeHomOverComp_coe] at hval
  exact Subtype.ext ((cancel_mono φ.1).1 hval)

theorem isCommutative_of_isHom_mono {LX : RelativeGroupLaw k fX} {LY : RelativeGroupLaw k fY}
    (hc : LY.IsCommutative) (φ : SchemeHomOver fX fY) [Mono φ.1] (h : IsHom LX LY φ) :
    LX.IsCommutative := by
  intro T t x y
  apply eq_of_comp_mono_eq φ
  rw [h t x y, h t y x, hc t]

/-- Transport of a relative group law along equality of structure morphisms. -/
def castLaw {f₁ f₂ : X ⟶ Spec (CommRingCat.of k)} (e : f₁ = f₂) (L : RelativeGroupLaw k f₁) :
    RelativeGroupLaw k f₂ :=
  e ▸ L

theorem castLaw_mul_val {f₁ f₂ : X ⟶ Spec (CommRingCat.of k)} (e : f₁ = f₂)
    (L : RelativeGroupLaw k f₁) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver t f₂) :
    ((castLaw e L).mul t x y).1 =
      (L.mul t ⟨x.1, by rw [e]; exact x.2⟩ ⟨y.1, by rw [e]; exact y.2⟩).1 := by
  subst e
  rfl

theorem castLaw_isCommutative {f₁ f₂ : X ⟶ Spec (CommRingCat.of k)} (e : f₁ = f₂)
    (L : RelativeGroupLaw k f₁) (hc : L.IsCommutative) : (castLaw e L).IsCommutative := by
  subst e
  exact hc

theorem castLaw_isHom {f₁ f₂ : X ⟶ Spec (CommRingCat.of k)} (e : f₁ = f₂)
    (L : RelativeGroupLaw k f₁) (LY : RelativeGroupLaw k fY) (φ : SchemeHomOver f₁ fY)
    (h : IsHom L LY φ) : IsHom (castLaw e L) LY ⟨φ.1, by rw [φ.2, e]⟩ := by
  subst e
  exact h

end Calculus

section Points
variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}

/-- The universal point given by the identity morphism. -/
abbrev idPt (f : G ⟶ Spec (CommRingCat.of k)) : SchemeHomOver f f := ⟨𝟙 G, Category.id_comp f⟩

/-- The constant point associated with a rational section. -/
def constPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : SchemeHomOver t f :=
  ⟨t ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩

@[scoped simp]
theorem constPt_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : (constPt t s).1 = t ≫ s.1 :=
  rfl

theorem comp_constPt {H : Scheme.{u}} {fH : H ⟶ Spec (CommRingCat.of k)} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t f)
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fH) :
    NeronModelInfra.schemeHomOverComp x (constPt f s) = constPt t s := by
  apply Subtype.ext
  simp only [NeronModelInfra.schemeHomOverComp_coe, constPt_coe, ← Category.assoc, x.2]

theorem constPt_id (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    constPt (𝟙 (Spec (CommRingCat.of k))) s = s :=
  Subtype.ext (Category.id_comp _)

theorem comp_idPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp x (idPt f) = x :=
  Subtype.ext (Category.comp_id _)

end Points

section Generic

theorem isIso_specMap_residue_genericPoint (X : Scheme.{u}) [IsIntegral X] :
    IsIso (Spec.map (X.residue (genericPoint X))) := by
  have hF : IsField (X.presheaf.stalk (genericPoint X)) :=
    isField_stalk_of_closure_mem_irreducibleComponents X _
      (by rw [genericPoint_closure, irreducibleComponents_eq_singleton]; exact Set.mem_singleton _)
  have hbij : Function.Bijective (X.residue (genericPoint X)) := by
    refine ⟨?_, X.residue_surjective _⟩
    change Function.Injective (IsLocalRing.residue (X.presheaf.stalk (genericPoint X)))
    rw [RingHom.injective_iff_ker_eq_bot, IsLocalRing.ker_residue,
      ← IsLocalRing.isField_iff_maximalIdeal_eq]
    exact hF
  have : IsIso (X.residue (genericPoint X)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  infer_instance

theorem isDominant_asFiberHom_genericPoint {X Y : Scheme.{u}} [IrreducibleSpace X] (q : X ⟶ Y) :
    IsDominant (q.asFiberHom (genericPoint X)) := by
  constructor
  rw [DenseRange, Scheme.Hom.range_asFiberHom, dense_iff_closure_eq]
  let e := q.fiberHomeo (q.base (genericPoint X))
  have he : e (q.asFiber (genericPoint X)) = ⟨genericPoint X, rfl⟩ :=
    e.apply_symm_apply _
  have h1 : closure ({(⟨genericPoint X, rfl⟩ : q.base ⁻¹' {q.base (genericPoint X)})} :
      Set (q.base ⁻¹' {q.base (genericPoint X)})) = Set.univ := by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.image_singleton]
    change Subtype.val ⁻¹' closure {genericPoint X} = Set.univ
    rw [genericPoint_closure]
    rfl
  have h2 := e.symm.image_closure {(⟨genericPoint X, rfl⟩ : q.base ⁻¹' {q.base (genericPoint X)})}
  rw [h1, Set.image_univ, Set.image_singleton, ← he, Homeomorph.symm_apply_apply,
    Set.range_eq_univ.mpr e.symm.surjective] at h2
  exact h2.symm

theorem flat_and_surjective_of_field {K k : Type u} [Field K] [Field k]
    (σ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) : Flat σ ∧ Surjective σ := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective σ
  refine ⟨?_, ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩⟩
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  let : Algebra k K := φ.hom.toAlgebra
  exact inferInstanceAs (Module.Flat k K)

end Generic

section FibreTorsor

variable {k : Type u} [Field k] {K : Type u} [Field K] {G A Q : Scheme.{u}}
  {f : G ⟶ Spec (CommRingCat.of k)} {fA : A ⟶ Spec (CommRingCat.of k)}
  {fQ : Q ⟶ Spec (CommRingCat.of k)}

/-- A point of a fibre of the quotient, viewed as a point of the original group. -/
def toG (q : SchemeHomOver f fQ) (ιη : Spec (CommRingCat.of K) ⟶ Q) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of K)} (v : SchemeHomOver t (pullback.snd q.1 ιη)) :
    SchemeHomOver (t ≫ ιη ≫ fQ) f :=
  ⟨v.1 ≫ pullback.fst q.1 ιη, by
    have h : pullback.fst q.1 ιη ≫ f = pullback.fst q.1 ιη ≫ q.1 ≫ fQ := by rw [q.2]
    rw [Category.assoc, h, pullback.condition_assoc, ← Category.assoc, v.2]⟩

@[scoped simp]
theorem toG_coe (q : SchemeHomOver f fQ) (ιη : Spec (CommRingCat.of K) ⟶ Q) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of K)} (v : SchemeHomOver t (pullback.snd q.1 ιη)) :
    (toG q ιη v).1 = v.1 ≫ pullback.fst q.1 ιη :=
  rfl

theorem toG_injective (q : SchemeHomOver f fQ) (ιη : Spec (CommRingCat.of K) ⟶ Q) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of K)} {v w : SchemeHomOver t (pullback.snd q.1 ιη)}
    (h : toG q ιη v = toG q ιη w) : v = w := by
  apply Subtype.ext
  apply pullback.hom_ext
  · exact congrArg Subtype.val h
  · exact v.2.trans w.2.symm

theorem comp_toG_q (q : SchemeHomOver f fQ) (ιη : Spec (CommRingCat.of K) ⟶ Q) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of K)} (v : SchemeHomOver t (pullback.snd q.1 ιη)) :
    (NeronModelInfra.schemeHomOverComp (toG q ιη v) q).1 = t ≫ ιη := by
  rw [NeronModelInfra.schemeHomOverComp_coe, toG_coe, Category.assoc, pullback.condition,
    ← Category.assoc, v.2]

theorem toG_transition (q : SchemeHomOver f fQ) (ιη : Spec (CommRingCat.of K) ⟶ Q) {T T' :
  Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of K)} {t' : T' ⟶ Spec (CommRingCat.of K)} (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (v : SchemeHomOver t (pullback.snd q.1 ιη)) :
    toG q ιη (GoodReductionJacobian.schemeHomOverComp ψ hψ v) =
      GoodReductionJacobian.schemeHomOverComp ψ (by rw [← Category.assoc, hψ]) (toG q ιη v) :=
  Subtype.ext (Category.assoc _ _ _)

/-- Translation in the ambient group. -/
def actG (L : RelativeGroupLaw k f) (jG : SchemeHomOver fA f) (q : SchemeHomOver f fQ)
    (ιη : Spec (CommRingCat.of K) ⟶ Q) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (a : SchemeHomOver t (RelativeGroupLaw.baseChangeStr (ιη ≫ fQ) fA))
    (v : SchemeHomOver t (pullback.snd q.1 ιη)) : SchemeHomOver (t ≫ ιη ≫ fQ) f :=
  L.mul (t ≫ ιη ≫ fQ)
    (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (ιη ≫ fQ) a) jG)
    (toG q ιη v)

variable (L : RelativeGroupLaw k f) (LA : RelativeGroupLaw k fA) (LQ : RelativeGroupLaw k fQ)
  (jG : SchemeHomOver fA f) (q : SchemeHomOver f fQ) (ιη : Spec (CommRingCat.of K) ⟶ Q)
  (hqker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp x q = LQ.one t ↔
      ∃ z : SchemeHomOver t fA, NeronModelInfra.schemeHomOverComp z jG = x)
  (hq : IsHom L LQ q)

include hqker hq in
theorem actG_comp_q {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (a : SchemeHomOver t (RelativeGroupLaw.baseChangeStr (ιη ≫ fQ) fA))
    (v : SchemeHomOver t (pullback.snd q.1 ιη)) :
    (actG L jG q ιη t a v).1 ≫ q.1 = t ≫ ιη := by
  have h : NeronModelInfra.schemeHomOverComp (actG L jG q ιη t a v) q =
      NeronModelInfra.schemeHomOverComp (toG q ιη v) q := by
    rw [actG, hq, (hqker _ _).mpr ⟨_, rfl⟩, LQ.one_mul]
  have := congrArg Subtype.val h
  rw [NeronModelInfra.schemeHomOverComp_coe] at this
  rw [this]
  exact comp_toG_q q ιη v

/-- Translation on the generic fiber of the quotient. -/
def act {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (a : SchemeHomOver t (RelativeGroupLaw.baseChangeStr (ιη ≫ fQ) fA))
    (v : SchemeHomOver t (pullback.snd q.1 ιη)) : SchemeHomOver t (pullback.snd q.1 ιη) :=
  ⟨pullback.lift (actG L jG q ιη t a v).1 t (actG_comp_q L LQ jG q ιη hqker hq t a v),
    pullback.lift_snd _ _ _⟩

theorem toG_act {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (a : SchemeHomOver t (RelativeGroupLaw.baseChangeStr (ιη ≫ fQ) fA))
    (v : SchemeHomOver t (pullback.snd q.1 ιη)) :
    toG q ιη (act L LQ jG q ιη hqker hq t a v) = actG L jG q ιη t a v :=
  Subtype.ext (pullback.lift_fst _ _ _)

theorem act_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (t' : T' ⟶ Spec (CommRingCat.of K)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (a : SchemeHomOver t (RelativeGroupLaw.baseChangeStr (ιη ≫ fQ) fA))
    (v : SchemeHomOver t (pullback.snd q.1 ιη)) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (act L LQ jG q ιη hqker hq t a v) =
      act L LQ jG q ιη hqker hq t' (GoodReductionJacobian.schemeHomOverComp ψ hψ a)
        (GoodReductionJacobian.schemeHomOverComp ψ hψ v) := by
  apply toG_injective q ιη
  rw [toG_transition, toG_act, toG_act, actG, actG, L.mul_natural, ← toG_transition q ιη ψ hψ v]
  rfl

theorem act_mul (hj : IsHom LA L jG) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (a b : SchemeHomOver t (RelativeGroupLaw.baseChangeStr (ιη ≫ fQ) fA))
    (v : SchemeHomOver t (pullback.snd q.1 ιη)) :
    act L LQ jG q ιη hqker hq t ((LA.baseChange (ιη ≫ fQ)).mul t a b) v =
      act L LQ jG q ιη hqker hq t a (act L LQ jG q ιη hqker hq t b v) := by
  apply toG_injective q ιη
  rw [toG_act, toG_act, actG, actG, toG_act, actG, RelativeGroupLaw.baseChangePointToBase_mul]
  rw [hj, L.mul_assoc]

theorem act_torsor [Mono jG.1] {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (v w : SchemeHomOver t (pullback.snd q.1 ιη)) :
    ∃! a : SchemeHomOver t (RelativeGroupLaw.baseChangeStr (ιη ≫ fQ) fA),
      act L LQ jG q ιη hqker hq t a v = w := by
  have hk : NeronModelInfra.schemeHomOverComp (L.mul _ (toG q ιη w) (L.inv _ (toG q ιη v))) q =
      LQ.one _ := by
    rw [hq, hq.inv]
    have : NeronModelInfra.schemeHomOverComp (toG q ιη w) q =
        NeronModelInfra.schemeHomOverComp (toG q ιη v) q :=
      Subtype.ext ((comp_toG_q q ιη w).trans (comp_toG_q q ιη v).symm)
    rw [this]
    exact LQ.mul_inv_cancel _ _
  obtain ⟨z, hz⟩ := (hqker _ _).mp hk
  refine ⟨RelativeGroupLaw.baseChangePointOfBase (ιη ≫ fQ) z, ?_, ?_⟩
  · apply toG_injective q ιη
    rw [toG_act, actG, RelativeGroupLaw.baseChangePointToBase_ofBase, hz, L.mul_assoc,
      L.inv_mul_cancel, L.mul_one]
  · intro b hb
    have h1 := congrArg (toG q ιη) hb
    rw [toG_act, actG] at h1
    have h2 : NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (ιη ≫ fQ)
      b) jG =
        NeronModelInfra.schemeHomOverComp z jG := by
      rw [hz]
      calc NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (ιη ≫ fQ) b) jG
          = L.mul _ (L.mul _ (NeronModelInfra.schemeHomOverComp
              (RelativeGroupLaw.baseChangePointToBase (ιη ≫ fQ) b) jG) (toG q ιη v))
              (L.inv _ (toG q ιη v)) := by
            rw [L.mul_assoc, L.mul_inv_cancel, L.mul_one]
        _ = L.mul _ (toG q ιη w) (L.inv _ (toG q ιη v)) := by rw [h1]
    have h3 : RelativeGroupLaw.baseChangePointToBase (ιη ≫ fQ) b = z := eq_of_comp_mono_eq jG h2
    rw [← h3, RelativeGroupLaw.baseChangePointOfBase_toBase]

end FibreTorsor

section BaseChangeNsmul

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
  (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem baseChangePointToBase_nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ)
    (x : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr ι f)) :
    RelativeGroupLaw.baseChangePointToBase ι ((G.baseChange ι).nsmul t' n x) =
      G.nsmul (t' ≫ ι) n (RelativeGroupLaw.baseChangePointToBase ι x) := by
  induction n with
  | zero => exact RelativeGroupLaw.baseChangePointToBase_one ι G t'
  | succ n ih =>
    rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ,
      RelativeGroupLaw.baseChangePointToBase_mul, ih]

end BaseChangeNsmul

section Main

theorem exists_retraction (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}}
    (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [Smooth f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    {A : Scheme.{u}} (j : A ⟶ G) [IsClosedImmersion j] [ConnectedSpace A] [IsProper (j ≫ f)]
    [Smooth (j ≫ f)] (LA : RelativeGroupLaw k (j ≫ f)) (hj : IsHom LA L ⟨j, rfl⟩) :
    ∃ (n : ℕ) (π : SchemeHomOver f (j ≫ f)), 0 < n ∧ IsHom L LA π ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (j ≫ f)),
        NeronModelInfra.schemeHomOverComp
            (NeronModelInfra.schemeHomOverComp x (⟨j, rfl⟩ : SchemeHomOver (j ≫ f) f)) π =
          LA.nsmul t n x := by
  classical
  set jG : SchemeHomOver (j ≫ f) f := ⟨j, rfl⟩ with hjG
  have hAc : LA.IsCommutative := isCommutative_of_isHom_mono hc jG hj
  have hAab : AbelianSchemePropertyBundle k (j ≫ f) :=
    ⟨inferInstance, inferInstance, fun s => by
      have : (j ≫ f).base ⁻¹' {s} = Set.univ := Set.eq_univ_of_forall fun _w => Subsingleton.elim _
          _
      rw [this]; exact isConnected_univ, ⟨LA⟩⟩
  obtain ⟨g, hg⟩ :=
    exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing L
  obtain ⟨a, ha⟩ :=
    exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing LA
  have hnormal : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f)
      (m : SchemeHomOver t (j ≫ f)), ∃ m' : SchemeHomOver t (j ≫ f),
        NeronModelInfra.schemeHomOverComp m' jG =
          L.mul t (L.mul t x (NeronModelInfra.schemeHomOverComp m jG)) (L.inv t x) := by
    intro T t x m
    refine ⟨m, ?_⟩
    let : CommGroup (SchemeHomOver t f) := L.pointCommGroup hc t
    change _ = x * _ * x⁻¹
    rw [mul_right_comm, _root_.mul_inv_cancel, _root_.one_mul]
  obtain ⟨Q, fQ, LQ, q, hQsep, hQqc, hQsm, -, hqsm, hqsurj, hqhom, hQcomm, hqker⟩ :=
    exists_quotient_smoothOfRelativeDimension_sub_of_isClosedImmersion_of_isAlgClosed
      k f L g j LA a hj hnormal
  have : Smooth q.1 := SmoothOfRelativeDimension.smooth a q.1
  have hqH : IsHom L LQ q := hqhom
  have : IrreducibleSpace G := by
    obtain ⟨G₀, i₀, -, hoi, -, hirr, -, -, hrange, -⟩ :=
      exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
        k L
    rw [PreconnectedSpace.connectedComponent_eq_univ, Set.range_eq_univ] at hrange
    rw [irreducibleSpace_def, Set.top_eq_univ, ← Set.image_univ_of_surjective hrange]
    exact IsIrreducible.image (IrreducibleSpace.isIrreducible_univ G₀) _ i₀.continuous.continuousOn
  have : IsReduced G := AlgebraicGeometry.isReduced_of_smooth_of_field f
  have : IsIntegral G := isIntegral_of_irreducibleSpace_of_isReduced G
  set η : G := genericPoint G with hη
  set y : Q := q.1.base η with hy
  let K : Type u := Q.residueField y
  let ιη : Spec (CommRingCat.of K) ⟶ Q := Q.fromSpecResidueField y
  let V : Scheme.{u} := pullback q.1 ιη
  let gV : V ⟶ Spec (CommRingCat.of K) := pullback.snd q.1 ιη
  let ιV : V ⟶ G := pullback.fst q.1 ιη
  have : Smooth gV := by change Smooth (pullback.snd _ _); infer_instance
  have : QuasiCompact q.1 :=
    MorphismProperty.of_postcomp (W := @QuasiCompact) (W' := @QuasiSeparated) q.1 fQ inferInstance
      (by rw [q.2]; infer_instance)
  have : QuasiCompact gV := by change QuasiCompact (pullback.snd _ _); infer_instance
  have : Nonempty V := ⟨show ↥(q.1.fiber y) from q.1.asFiber η⟩
  have : IsReduced V := AlgebraicGeometry.isReduced_of_smooth_of_field gV
  obtain ⟨K', _, _, _, _, P', hP'⟩ :=
    AlgebraicGeometry.exists_isSeparable_specMap_comp_eq_of_smooth_of_nonempty K gV
  let F₀ := SeparableClosure K
  let φ₀ : K' →ₐ[K] F₀ := IsSepClosed.lift
  let : Algebra K' F₀ := φ₀.toRingHom.toAlgebra
  have : IsScalarTower K K' F₀ := IsScalarTower.of_algebraMap_eq fun x => (φ₀.commutes x).symm
  let K'' := IntermediateField.normalClosure K K' F₀
  let P : Spec (CommRingCat.of K'') ⟶ V := Spec.map (CommRingCat.ofHom (algebraMap K' K'')) ≫ P'
  have hP : P ≫ gV = Spec.map (CommRingCat.ofHom (algebraMap K K'')) := by
    simp only [P, Category.assoc, hP', ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
  have : IsSeparated (RelativeGroupLaw.baseChangeStr (ιη ≫ fQ) (j ≫ f)) := by
    change IsSeparated (pullback.snd _ _); infer_instance
  have : LocallyOfFiniteType (RelativeGroupLaw.baseChangeStr (ιη ≫ fQ) (j ≫ f)) := by
    change LocallyOfFiniteType (pullback.snd _ _); infer_instance
  obtain ⟨φ, hφ⟩ :=
    exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois
      K (RelativeGroupLaw.baseChangeStr (ιη ≫ fQ) (j ≫ f)) (LA.baseChange (ιη ≫ fQ))
      (hAc.baseChange _) gV
      (fun t => act L LQ jG q ιη hqker hqH t)
      (act_natural L LQ jG q ιη hqker hqH) (act_mul L LA LQ jG q ιη hqker hqH hj)
      (act_torsor L LQ jG q ιη hqker hqH) K'' P hP
  set nn : ℕ := Module.finrank K K'' with hnn_def
  have hnn : 0 < nn := Module.finrank_pos
  let φA : V ⟶ A := φ.1 ≫ pullback.fst (j ≫ f) (ιη ≫ fQ)
  have hιVf : ιV ≫ f = gV ≫ ιη ≫ fQ := by
    have h : ιV ≫ f = ιV ≫ q.1 ≫ fQ := by rw [q.2]
    rw [h]
    exact pullback.condition_assoc _
  have hφAf : φA ≫ j ≫ f = ιV ≫ f := by
    simp only [φA, Category.assoc]
    rw [pullback.condition, ← Category.assoc, φ.2, hιVf]
  let ξ : Spec (G.residueField η) ⟶ V := q.1.asFiberHom η
  have hξι : ξ ≫ ιV = G.fromSpecResidueField η := q.1.asFiberHom_fiberι η
  have : IsDominant ξ := isDominant_asFiberHom_genericPoint q.1
  have hres : IsIso (Spec.map (G.residue η)) := isIso_specMap_residue_genericPoint G
  let φst : Spec (G.presheaf.stalk η) ⟶ A := CategoryTheory.inv (Spec.map (G.residue η)) ≫ ξ ≫ φA
  have hφst : φst ≫ (j ≫ f) = G.fromSpecStalk η ≫ f := by
    simp only [φst, Category.assoc]
    rw [hφAf, ← Category.assoc ξ ιV f, hξι, Scheme.fromSpecResidueField, Category.assoc,
      IsIso.inv_hom_id_assoc]
  obtain ⟨U, hηU, fU, hfU1, hfU2⟩ := spread_out_of_isGermInjective' f (j ≫ f) φst hφst
  have : Nonempty U.toScheme := ⟨(⟨η, hηU⟩ : U)⟩
  obtain ⟨ψ, hψ1, hψ2⟩ :=
    AlgebraicGeometry.exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle f hAab U.ι
      fU hfU2
  have hVψ : ιV ≫ ψ = φA := by
    refine ext_of_isDominant_of_isSeparated (j ≫ f) ?_ ξ ?_
    · rw [Category.assoc, hψ1, hφAf]
    · rw [← Category.assoc, hξι, Scheme.fromSpecResidueField, Category.assoc,
        ← Scheme.Opens.fromSpecStalkOfMem_ι U η hηU, Category.assoc, hψ2, ← hfU1]
      simp only [φst, IsIso.hom_inv_id_assoc]
  let ψpt : SchemeHomOver f (j ≫ f) := ⟨ψ, hψ1⟩
  let c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (j ≫ f) :=
    NeronModelInfra.schemeHomOverComp (L.one (𝟙 _)) ψpt
  let π : SchemeHomOver f (j ≫ f) := LA.mul f ψpt (LA.inv f (constPt f c))
  have hπe : NeronModelInfra.schemeHomOverComp (L.one (𝟙 (Spec (CommRingCat.of k)))) π =
      LA.one (𝟙 (Spec (CommRingCat.of k))) := by
    simp only [π]
    rw [comp_lawMul, comp_lawInv, comp_constPt, constPt_id]
    exact LA.mul_inv_cancel _ _
  have hπhom : IsHom L LA π :=
    comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
      k L LA hAab π hπe
  have hψπ : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp x ψpt =
        LA.mul t (NeronModelInfra.schemeHomOverComp x π) (constPt t c) := by
    intro T t x
    simp only [π]
    rw [comp_lawMul, comp_lawInv, comp_constPt, LA.mul_assoc, LA.inv_mul_cancel, LA.mul_one]
  have hkey : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (a₀ : SchemeHomOver (t ≫ ιη ≫ fQ) (j ≫ f)) (v : SchemeHomOver t gV),
      NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a₀ jG) π =
        LA.nsmul _ nn a₀ := by
    intro T t a₀ v
    let : CommGroup (SchemeHomOver (t ≫ ιη ≫ fQ) (j ≫ f)) :=
      LA.pointCommGroup hAc (t ≫ ιη ≫ fQ)
    have h1 := congrArg (RelativeGroupLaw.baseChangePointToBase (ιη ≫ fQ))
      (hφ t (RelativeGroupLaw.baseChangePointOfBase (ιη ≫ fQ) a₀) v)
    rw [RelativeGroupLaw.baseChangePointToBase_mul, baseChangePointToBase_nsmul,
      RelativeGroupLaw.baseChangePointToBase_ofBase] at h1
    have hVψ' : φ.1 ≫ pullback.fst (j ≫ f) (ιη ≫ fQ) = pullback.fst q.1 ιη ≫ ψ := hVψ.symm
    have eL : RelativeGroupLaw.baseChangePointToBase (ιη ≫ fQ)
        (NeronModelInfra.schemeHomOverComp
          (act L LQ jG q ιη hqker hqH t (RelativeGroupLaw.baseChangePointOfBase (ιη ≫ fQ) a₀) v)
            φ) =
        NeronModelInfra.schemeHomOverComp
          (L.mul _ (NeronModelInfra.schemeHomOverComp a₀ jG) (toG q ιη v)) ψpt := by
      apply Subtype.ext
      have := congrArg Subtype.val
        (toG_act L LQ jG q ιη hqker hqH t (RelativeGroupLaw.baseChangePointOfBase (ιη ≫ fQ) a₀) v)
      simp only [toG_coe] at this
      simp only [RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe,
        Category.assoc]
      rw [hVψ', ← Category.assoc, this, actG, RelativeGroupLaw.baseChangePointToBase_ofBase]
    have eR : RelativeGroupLaw.baseChangePointToBase (ιη ≫ fQ) (NeronModelInfra.schemeHomOverComp
      v φ) =
        NeronModelInfra.schemeHomOverComp (toG q ιη v) ψpt := by
      apply Subtype.ext
      simp only [RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe,
        Category.assoc, toG_coe]
      rw [hVψ']
    rw [eL, eR, hψπ, hψπ, hπhom] at h1
    set X := NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a₀ jG) π
    set Y := NeronModelInfra.schemeHomOverComp (toG q ιη v) π
    set C := constPt (t ≫ ιη ≫ fQ) c
    set N := LA.nsmul (t ≫ ιη ≫ fQ) nn a₀
    change X * Y * C = Y * C * N at h1
    have h2 : X * (Y * C) = N * (Y * C) := by rw [← _root_.mul_assoc, h1, mul_comm _ N]
    exact mul_right_cancel h2
  obtain ⟨hσfl, hσsurj⟩ := flat_and_surjective_of_field (K := K) (k := k) (ιη ≫ fQ)
  have : Flat (ιη ≫ fQ) := hσfl
  have : Surjective (ιη ≫ fQ) := hσsurj
  have : Surjective gV := ⟨fun p => ⟨Classical.arbitrary V, Subsingleton.elim _ _⟩⟩
  have : Flat (gV ≫ ιη ≫ fQ) := inferInstance
  have : Surjective (gV ≫ ιη ≫ fQ) := inferInstance
  have : Epi (pullback.fst (j ≫ f) (gV ≫ ιη ≫ fQ)) := Flat.epi_of_flat_of_surjective _
  have hE : j ≫ π.1 = LA.schemeNsmul nn := by
    rw [← cancel_epi (pullback.fst (j ≫ f) (gV ≫ ιη ≫ fQ))]
    let t₀ : pullback (j ≫ f) (gV ≫ ιη ≫ fQ) ⟶ Spec (CommRingCat.of K) := pullback.snd _ _ ≫ gV
    let a₀ : SchemeHomOver (t₀ ≫ ιη ≫ fQ) (j ≫ f) :=
      ⟨pullback.fst _ _, by simp only [t₀, Category.assoc]; exact pullback.condition⟩
    let v₀ : SchemeHomOver t₀ gV := ⟨pullback.snd _ _, rfl⟩
    have h := congrArg Subtype.val (hkey t₀ a₀ v₀)
    have h' := congrArg Subtype.val (comp_lawNsmul LA a₀ nn (idPt (j ≫ f)))
    rw [comp_idPt] at h'
    rw [← h'] at h
    simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc] at h
    exact h
  refine ⟨nn, π, hnn, hπhom, fun t x => ?_⟩
  apply Subtype.ext
  have h' := congrArg Subtype.val (comp_lawNsmul LA x nn (idPt (j ≫ f)))
  rw [comp_idPt] at h'
  rw [← h']
  simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
  change x.1 ≫ j ≫ π.1 = x.1 ≫ LA.schemeNsmul nn
  rw [hE]

end Main

end RetractionConstruction

end
end AbelianVarieties.NOSProofs.RosenlichtRetractions

namespace GoodReductionJacobian.RelativeGroupLaw
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AbelianVarieties.NOSProofs.RosenlichtRetractions.RetractionConstruction
universe u

theorem exists_retraction_up_to_nsmul_of_proper_subgroup
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [Smooth f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    {A : Scheme.{u}} (j : A ⟶ G) [IsClosedImmersion j] [ConnectedSpace A] [IsProper (j ≫ f)]
    [Smooth (j ≫ f)] (LA : RelativeGroupLaw k (j ≫ f))
    (hj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (j ≫ f)),
      NeronModelInfra.schemeHomOverComp (LA.mul t x y) (⟨j, rfl⟩ : SchemeHomOver (j ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨j, rfl⟩ : SchemeHomOver (j ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨j, rfl⟩ : SchemeHomOver (j ≫ f) f))) :
    ∃ (n : ℕ) (π : SchemeHomOver f (j ≫ f)), 0 < n ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
        NeronModelInfra.schemeHomOverComp (L.mul t x y) π =
          LA.mul t (NeronModelInfra.schemeHomOverComp x π)
            (NeronModelInfra.schemeHomOverComp y π)) ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (j ≫ f)),
        NeronModelInfra.schemeHomOverComp
            (NeronModelInfra.schemeHomOverComp x (⟨j, rfl⟩ : SchemeHomOver (j ≫ f) f)) π =
          LA.nsmul t n x := by
  obtain ⟨n, π, hn, hπ, hπj⟩ := exists_retraction k f L hc j LA hj
  exact ⟨n, π, hn, hπ, hπj⟩

end GoodReductionJacobian.RelativeGroupLaw
end
